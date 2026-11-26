// Supply-Cleanse Velocity Compounder — pump.fun paper sprint bot.
//
// Strategy (inside the field's convergent grammar, plus one twist):
//   * Early supply-cleanse entry: a fresh coin is watched from its
//     CreateEvent. We only buy after early sellers have flushed some
//     supply (cumulative sell volume observed) AND the tape turns
//     buyer-dominated (buy share of recent flow >= 60%).
//   * Pullback-breakout trigger: the price must be up >= 3% from where
//     we first saw it, have dipped >= 2% off its running high, and then
//     reclaimed >= 3% off that dip low. We buy the reclaim, not the top.
//   * Graduation-aware exits: take profit at +18%, a trailing stop
//     once the trade is +10% (sell on a 6% fall from the peak), a hard
//     stop at -8%, a max hold of ~40 minutes in slots, and an immediate
//     exit on CompleteEvent (the curve graduates; the bonding-curve
//     game ends). Hot coins can be re-entered after a short cooldown,
//     up to 4 entries per coin.
//   * Sizing: each buy is min(0.40 SOL, 100 bps of the coin's real SOL
//     reserve) — the harness rejects anything over the cap, which is
//     what killed v1 (300 buys, 0 fills).
//   * Twist — second-wave re-entry: after a profitable exit, if the coin
//     pulls back >= 10% from our exit price while buyers still dominate
//     the tape, we re-enter once at half stake.
//
// Protocol: the harness speaks agent-fun/replay/v2 over NDJSON on
// stdin. It sends a hello line, then one batch per step (each batch
// carries its seq, its slot, the events, marks, fills and the account),
// then a done line. We answer every batch with exactly one reply
// echoing its seq and carrying our orders for that batch. A batch may
// hold at most 16 orders; at most 5 positions may be open; buys on one
// mint in one reply may spend at most 100 bps of its real SOL reserve.
// All amounts are u64 decimal strings; we do the maths in BigInt and
// only use floats for price ratios. Everything is deterministic: no
// clock, no randomness, ties break on mint id, so two runs of the same
// input produce byte-identical orders.
//
// Run: node main.ts  (Node 22+ runs TypeScript as-is; stdlib only).

import { createInterface } from "node:readline";

// ---------------------------------------------------------------- tuning
const MIN_BUY_LAMPORTS = 20_000_000n; // 0.02 SOL: smallest buy worth fees
const MIN_ROUND_TRIP_LAMPORTS = 10_000_000n; // guardrail: 0.01 SOL
const MAX_SLIPPAGE_BPS = 2000; // 20%: fills survive 2-slot latency
const MAX_ORDERS_PER_BATCH = 16;
const MAX_OPEN_POSITIONS = 5;

const ENTRY_MIN_RISE = 0.03; // price up >= 3% vs first sighting. v6's
  // ignition entry (+2%, no dip wait) fired 32k attempts at a 28% win
  // rate (-1.53 SOL); the dip/reclaim filter of v3 was better (-0.94).
const ENTRY_MIN_BUY_SHARE = 0.60; // buyers >= 60% of recent flow
const ENTRY_MIN_TRADES = 10; // trades observed before we trust a coin
const ENTRY_MIN_SELL_SOL = 50_000_000n; // 0.05 SOL sold = supply cleansed
const ENTRY_DIP = 0.02; // price dipped >= 2% off its running high
const ENTRY_RECLAIM = 0.03; // ...and reclaimed >= 3% off the dip low
const ENTRY_MAX_MC_SOL = 80; // skip coins already near graduation
const ENTRY_MIN_MC_SOL = 30; // skip coins with no curve built yet
const ENTRY_MAX_AGE_SLOTS = 20000; // coin must still be young (~2.2h)
const MAX_ENTRIES_PER_COIN = 4; // re-entries per coin, cap churn
const REENTRY_COOLDOWN_SLOTS = 300; // pause after an exit before re-buying
const STAKE_LAMPORTS = 400_000_000n; // 0.40 SOL target buy (cap-bound)

const TAKE_PROFIT = 0.18; // sell all at +18% (v7 params: best of the
  // family; v9's looser +25%/15% trail lost more, -1.16 SOL)
const TRAIL_ARM = 0.10; // trailing stop arms at +10%...
const TRAIL_GIVEBACK = 0.06; // ...and fires on a 6% fall from peak
const STOP_LOSS = -0.08; // hard stop at -8%
const MAX_HOLD_SLOTS = 6000; // ~40 minutes, then exit regardless
const SELL_RETRY_COOLDOWN_SLOTS = 200; // pause after a rejected sell

const REENTRY_PULLBACK = 0.10; // re-enter >= 10% below our exit price
const REENTRY_MIN_BUY_SHARE = 0.65; // ...only while buyers dominate

const RECENT_TRADES = 20; // window for the buy-share filter
const PRUNE_AGE_SLOTS = 40000; // drop stale unwatched coins

// ---------------------------------------------------------------- types
type U64 = string;
type AnyMsg = Record<string, any>;

interface TradeFlow {
  buy: boolean;
  sol: bigint;
}

interface Coin {
  mint: string;
  firstSlot: number;
  firstPrice: number; // SOL per token base unit, first seen
  highPrice: number; // running high since creation
  lowSinceHigh: number; // lowest price since the running high was set
  lastPrice: number;
  lastTradeSlot: number;
  realSol: bigint; // real SOL reserves (the size-cap basis)
  tradeCount: number;
  totalBuySol: bigint;
  totalSellSol: bigint;
  recent: TradeFlow[]; // last RECENT_TRADES trades
  complete: boolean;
  decided: boolean; // entered once (or skipped for good)
  reentryDone: boolean;
  dead: boolean; // sell permanently refused (e.g. token_complete):
    // the harness flattens it at done; stop spamming sells for it
  sellCooldownUntil: number; // slot before which we will not re-sell
  entries: number; // buys taken on this coin so far
  cooldownUntil: number; // slot before which we will not re-buy
  exitPrice: number; // price of our last (profitable) exit, 0 if none
  exitWasProfit: boolean;
  entrySlot: number; // slot of our current position, 0 if flat
  peakRatio: number; // best value/cost ratio seen on current position
}

interface Position {
  mint: string;
  tokens: bigint;
  cost: bigint;
}

// ---------------------------------------------------------------- state
let capitalLamports = 10_000_000_000n;
let maxOpenPositions = MAX_OPEN_POSITIONS;
let maxOrdersPerBatch = MAX_ORDERS_PER_BATCH;
let maxOrderBps = 100;
let txFeeLamports = 105_000n;
let feeBps = 125; // protocol + creator fallback, for cash planning
let orderCounter = 0;
// Buys in flight: ordered but not yet visible in the account snapshot
// (fills land ~2 slots after the decision batch). They still occupy a
// position slot — ignoring them over-orders past the 5-position cap
// and the extra buys come back rejected.
let inflightBuys = new Map<string, number>(); // mint -> batch seq
// Sells in flight: same problem on the exit side. Without this, a sell
// is re-issued every batch until its fill lands, and the duplicates
// come back rejected (v6: 31k rejected sells).
let inflightSells = new Map<string, number>(); // mint -> batch seq
let currentSeq = 0;

const coins = new Map<string, Coin>();
const held = new Map<string, Position>(); // from the latest account

function priceOf(vsol: U64 | undefined, vtok: U64 | undefined): number {
  if (!vsol || !vtok) return 0;
  const s = BigInt(vsol);
  const t = BigInt(vtok);
  if (t === 0n || s === 0n) return 0;
  return Number(s) / Number(t);
}

function marketCapSol(coin: Coin): number {
  // price (SOL per base unit) * total supply; pump.fun supply is 1e9
  // tokens, and the curve quotes in base units, so MC ~ price * 1e15
  // base units. We track it in SOL via the first-seen supply-free
  // shortcut: MC = vsol/vtok * 1e15 lamports... expressed in SOL as
  // price * 1e15 / 1e9. Kept as a ratio against the creation MC instead:
  // creation MC is ~30 SOL, so MC_SOL ~= 30 * price / firstPrice.
  if (coin.firstPrice <= 0) return 0;
  return 30 * (coin.lastPrice / coin.firstPrice);
}

function buyShare(coin: Coin): number {
  let buy = 0n;
  let total = 0n;
  for (const t of coin.recent) {
    total += t.sol;
    if (t.buy) buy += t.sol;
  }
  if (total === 0n) return 0;
  return Number((buy * 10000n) / total) / 10000;
}

function nextClientId(kind: string): string {
  orderCounter += 1;
  return `${kind}-${orderCounter}`;
}

// ---------------------------------------------------------------- events
function onCreate(ev: AnyMsg, slot: number): void {
  const mint = ev.mint as string;
  if (coins.has(mint)) return;
  const p = priceOf(ev.virtual_sol_reserves, ev.virtual_token_reserves);
  coins.set(mint, {
    mint,
    firstSlot: slot,
    firstPrice: p,
    highPrice: p,
    lowSinceHigh: p,
    lastPrice: p,
    lastTradeSlot: slot,
    realSol: BigInt((ev.real_sol_reserves as U64) ?? "0"),
    tradeCount: 0,
    totalBuySol: 0n,
    totalSellSol: 0n,
    recent: [],
    complete: false,
    decided: false,
    reentryDone: false,
    dead: false,
    sellCooldownUntil: 0,
    entries: 0,
    cooldownUntil: 0,
    exitPrice: 0,
    exitWasProfit: false,
    entrySlot: 0,
    peakRatio: 1,
  });
}

function onTrade(ev: AnyMsg, slot: number): void {
  const mint = ev.mint as string;
  let coin = coins.get(mint);
  if (!coin) {
    // A coin whose CreateEvent we missed (sample boundary): seed it
    // from the trade itself so it can still be traded.
    const p0 = priceOf(ev.virtual_sol_reserves, ev.virtual_token_reserves);
    coin = {
      mint,
      firstSlot: slot,
      firstPrice: p0,
      highPrice: p0,
      lowSinceHigh: p0,
      lastPrice: p0,
      lastTradeSlot: slot,
      realSol: BigInt((ev.real_sol_reserves as U64) ?? "0"),
      tradeCount: 0,
      totalBuySol: 0n,
      totalSellSol: 0n,
      recent: [],
      complete: false,
      decided: false,
      reentryDone: false,
      dead: false,
      sellCooldownUntil: 0,
      entries: 0,
      cooldownUntil: 0,
      exitPrice: 0,
      exitWasProfit: false,
      entrySlot: 0,
      peakRatio: 1,
    };
    coins.set(mint, coin);
  }
  const p = priceOf(ev.virtual_sol_reserves, ev.virtual_token_reserves);
  if (p > 0) {
    coin.lastPrice = p;
    if (p > coin.highPrice) {
      coin.highPrice = p;
      coin.lowSinceHigh = p;
    } else if (p < coin.lowSinceHigh) {
      coin.lowSinceHigh = p;
    }
  }
  const sol = BigInt(ev.sol_amount as U64);
  coin.realSol = BigInt(ev.real_sol_reserves as U64);
  if (ev.is_buy) coin.totalBuySol += sol;
  else coin.totalSellSol += sol;
  coin.recent.push({ buy: !!ev.is_buy, sol });
  if (coin.recent.length > RECENT_TRADES) coin.recent.shift();
  coin.tradeCount += 1;
  coin.lastTradeSlot = slot;
}

function onComplete(ev: AnyMsg): void {
  const coin = coins.get(ev.mint as string);
  if (coin) coin.complete = true;
}

// ---------------------------------------------------------------- orders
function decide(batch: AnyMsg): AnyMsg[] {
  const orders: AnyMsg[] = [];
  const slot = batch.slot as number;
  currentSeq = batch.seq as number;

  // Refresh holdings from the authoritative account snapshot, and
  // refresh prices from the marks (latest curve state per mint).
  held.clear();
  for (const pos of batch.account?.positions ?? []) {
    held.set(pos.mint as string, {
      mint: pos.mint as string,
      tokens: BigInt(pos.token_amount as U64),
      cost: BigInt(pos.cost_lamports as U64),
    });
  }
  for (const mark of batch.marks ?? []) {
    const coin = coins.get(mark.mint as string);
    if (!coin) continue;
    coin.realSol = BigInt(mark.real_quote_reserves as U64);
    const p = priceOf(mark.virtual_quote_reserves, mark.virtual_token_reserves);
    if (p > 0) {
      coin.lastPrice = p;
      if (p > coin.highPrice) {
        coin.highPrice = p;
        coin.lowSinceHigh = p;
      } else if (p < coin.lowSinceHigh) {
        coin.lowSinceHigh = p;
      }
    }
  }

  // Clear buys that have now landed from the in-flight set; a
  // rejected/failed buy frees its coin to be tried again instead of
  // burning it as decided. Likewise clear sells that have settled.
  for (const fill of batch.fills ?? []) {
    if (fill.side === "buy") {
      inflightBuys.delete(fill.mint as string);
      if (fill.status !== "filled") {
        const c = coins.get(fill.mint as string);
        if (c && !held.has(fill.mint as string)) c.decided = false;
      }
    } else if (fill.side === "sell") {
      inflightSells.delete(fill.mint as string);
      const c = coins.get(fill.mint as string);
      if (c && fill.status !== "filled") {
        // A sell the harness refuses for token_complete will never
        // succeed: the position is flattened at done, so stop trying.
        // Any other rejection gets a retry cooldown instead of a
        // re-issue every batch (v9 spammed 21k rejected sells this way).
        if (fill.reason === "token_complete") {
          c.complete = true;
          c.dead = true;
        } else {
          c.sellCooldownUntil = slot + SELL_RETRY_COOLDOWN_SLOTS;
        }
      }
    }
  }
  // A buy rejected by the harness never produces a fill; drop it from
  // the in-flight set once it is clearly stale so the slot frees up,
  // and un-decide the coin so a later batch can try it again.
  // (Same for a sell whose fill record never arrives.)
  for (const [mint, seq] of inflightBuys) {
    if (currentSeq - seq > 30) {
      inflightBuys.delete(mint);
      const c = coins.get(mint);
      if (c && !held.has(mint)) c.decided = false;
    }
  }
  for (const [mint, seq] of inflightSells) {
    if (currentSeq - seq > 30) inflightSells.delete(mint);
  }

  let cash = BigInt(batch.account?.cash_lamports ?? "0");
  const committed = new Set<string>(held.keys());
  for (const mint of inflightBuys.keys()) committed.add(mint);

  const pushSell = (mint: string, tokens: bigint, exitPrice: number, profit: boolean): void => {
    if (orders.length >= maxOrdersPerBatch) return;
    if (tokens <= 0n) return;
    if (inflightSells.has(mint)) return; // sell already on its way
    const id = nextClientId("sell");
    inflightSells.set(mint, currentSeq);
    orders.push({
      side: "sell",
      client_id: id,
      mint,
      token_amount: tokens.toString(),
      max_slippage_bps: MAX_SLIPPAGE_BPS,
    });
    const coin = coins.get(mint);
    if (coin) {
      coin.exitPrice = exitPrice;
      coin.exitWasProfit = profit;
      coin.entrySlot = 0;
      coin.peakRatio = 1;
      // The coin is tradable again after a short cooldown: compounders
      // re-enter hot coins instead of burning them after one trade.
      coin.decided = false;
      coin.cooldownUntil = slot + REENTRY_COOLDOWN_SLOTS;
    }
    committed.delete(mint);
  };

  // ---- exits first: graduation, profit, trailing stop, hard stop, age.
  for (const [mint, pos] of held) {
    const coin = coins.get(mint);
    if (!coin || pos.cost === 0n || coin.lastPrice <= 0) continue;
    if (coin.dead || slot < coin.sellCooldownUntil) continue;
    const entryPrice = Number(pos.cost) / Number(pos.tokens);
    const ratio = coin.lastPrice / entryPrice; // value / cost
    if (ratio > coin.peakRatio) coin.peakRatio = ratio;
    const pnl = ratio - 1;
    const agedOut = coin.entrySlot > 0 && slot - coin.entrySlot > MAX_HOLD_SLOTS;
    let sell = false;
    let reason = "";
    if (coin.complete) {
      sell = true;
      reason = "graduation";
    } else if (pnl >= TAKE_PROFIT) {
      sell = true;
      reason = "take-profit";
    } else if (coin.peakRatio >= 1 + TRAIL_ARM && ratio <= coin.peakRatio * (1 - TRAIL_GIVEBACK)) {
      sell = true;
      reason = "trailing-stop";
    } else if (pnl <= STOP_LOSS) {
      sell = true;
      reason = "stop-loss";
    } else if (agedOut) {
      sell = true;
      reason = "max-hold";
    }
    void reason;
    if (sell) pushSell(mint, pos.tokens, coin.lastPrice, pnl > 0);
  }

  // ---- entries: rank candidates by velocity score, fill free slots.
  let freeSlots = maxOpenPositions - committed.size;
  if (freeSlots > 0) {
    const scored: { coin: Coin; score: number; amount: bigint }[] = [];
    for (const coin of coins.values()) {
      if (coin.complete || committed.has(coin.mint)) continue;
      if (coin.entries >= MAX_ENTRIES_PER_COIN) continue;
      if (slot < coin.cooldownUntil) continue;
      // A decided coin is done — except a profitable exit that has not
      // used its one second-wave re-entry yet; that coin stays eligible.
      const reentryOpen = coin.exitWasProfit && !coin.reentryDone;
      if (coin.decided && !reentryOpen) continue;
      if (slot - coin.firstSlot > ENTRY_MAX_AGE_SLOTS) continue;
      if (coin.tradeCount < ENTRY_MIN_TRADES) continue;
      if (coin.firstPrice <= 0 || coin.lastPrice <= 0) continue;
      const rise = coin.lastPrice / coin.firstPrice - 1;
      const mc = marketCapSol(coin);
      if (mc < ENTRY_MIN_MC_SOL || mc > ENTRY_MAX_MC_SOL) continue;
      if (coin.totalSellSol < ENTRY_MIN_SELL_SOL) continue; // not cleansed
      const share = buyShare(coin);
      if (share < ENTRY_MIN_BUY_SHARE) continue;
      const dipped = coin.lowSinceHigh <= coin.highPrice * (1 - ENTRY_DIP);
      const reclaimed = coin.lastPrice >= coin.lowSinceHigh * (1 + ENTRY_RECLAIM);
      const isReentry =
        coin.exitWasProfit &&
        !coin.reentryDone &&
        coin.exitPrice > 0 &&
        coin.lastPrice <= coin.exitPrice * (1 - REENTRY_PULLBACK) &&
        share >= REENTRY_MIN_BUY_SHARE;
      // Fresh entry needs momentum + pullback-reclaim; a re-entry only
      // needs the pullback below our exit price plus buyer dominance.
      if (!isReentry && (rise < ENTRY_MIN_RISE || !dipped || !reclaimed)) continue;
      if (isReentry && rise < ENTRY_MIN_RISE) continue;
      // The per-reply size cap is 100 bps of the mint's real SOL
      // reserve at decision time (hello.caps). Buy min(stake, cap):
      // asking for more gets the whole order rejected, which is what
      // killed v1 (300 buys, 0 fills). A re-entry takes half stake.
      // If the cap is below the minimum buy, skip the coin for now —
      // the cap grows with volume, and the coin stays undecided.
      const cap = coin.realSol / 100n;
      let amount = STAKE_LAMPORTS;
      if (isReentry) amount = STAKE_LAMPORTS / 2n;
      if (amount > cap) amount = cap;
      if (amount < MIN_BUY_LAMPORTS) continue;
      const score = rise * 2 + share + Math.log10(Number(coin.totalBuySol) + 1) / 10;
      scored.push({ coin, score, amount });
    }
    scored.sort((a, b) => b.score - a.score || (a.coin.mint < b.coin.mint ? -1 : 1));
    for (const { coin, amount } of scored) {
      if (freeSlots <= 0 || orders.length >= maxOrdersPerBatch) break;
      const cost = amount + txFeeLamports + (amount * BigInt(feeBps)) / 10000n;
      if (cash < cost) continue;
      const id = nextClientId("buy");
      orders.push({
        side: "buy",
        client_id: id,
        mint: coin.mint,
        quote_lamports: amount.toString(),
        max_slippage_bps: MAX_SLIPPAGE_BPS,
      });
      cash -= cost;
      committed.add(coin.mint);
      inflightBuys.set(coin.mint, currentSeq);
      coin.decided = true;
      coin.entries += 1;
      coin.entrySlot = slot;
      coin.peakRatio = 1;
      if (coin.exitWasProfit) coin.reentryDone = true;
      freeSlots -= 1;
    }
  }

  // Prune stale coins so memory stays bounded over a long window.
  if (coins.size > 20000) {
    for (const [mint, coin] of coins) {
      if (!held.has(mint) && slot - coin.lastTradeSlot > PRUNE_AGE_SLOTS) {
        coins.delete(mint);
      }
    }
  }

  return orders;
}

// ---------------------------------------------------------------- driver
async function main(): Promise<void> {
  const rl = createInterface({ input: process.stdin, crlfDelay: Infinity });
  for await (const line of rl) {
    if (!line.trim()) continue;
    let msg: AnyMsg;
    try {
      msg = JSON.parse(line) as AnyMsg;
    } catch {
      continue; // never die on a malformed line; the run must finish
    }
    if (msg.type === "hello") {
      capitalLamports = BigInt(msg.capital?.lamports ?? "10000000000");
      maxOpenPositions = msg.caps?.max_open_positions ?? MAX_OPEN_POSITIONS;
      maxOrdersPerBatch = msg.caps?.max_orders_per_batch ?? MAX_ORDERS_PER_BATCH;
      maxOrderBps = msg.caps?.max_order_bps_of_real_reserve ?? 100;
      txFeeLamports =
        BigInt(msg.fees?.base_fee_lamports ?? "5000") +
        BigInt(msg.fees?.priority_fee_lamports ?? "100000");
      feeBps =
        (msg.fees?.protocol_bps_fallback ?? 95) +
        (msg.fees?.creator_bps_fallback ?? 30);
      void capitalLamports;
      void maxOrderBps;
      continue; // hello takes no reply
    }
    if (msg.type === "batch") {
      for (const ev of msg.events ?? []) {
        if (ev.event === "CreateEvent") onCreate(ev, msg.slot);
        else if (ev.event === "TradeEvent") onTrade(ev, msg.slot);
        else if (ev.event === "CompleteEvent") onComplete(ev);
      }
      const orders = decide(msg);
      process.stdout.write(
        JSON.stringify({ type: "reply", seq: msg.seq, orders }) + "\n",
      );
      continue;
    }
    if (msg.type === "done") {
      break; // positions are flattened by the harness; exit cleanly
    }
  }
}

main().catch(() => process.exit(1));
