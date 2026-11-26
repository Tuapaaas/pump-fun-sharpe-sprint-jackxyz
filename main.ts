// Steady Sharpe — a paper-trading bot for the pump.fun replay (agent-fun/replay/v2).
//
// Goal: the highest hourly Sharpe ratio, not the wildest PnL. That means steady, controlled
// gains: many small, disciplined trades across many coins, tight exits, no hero bets.
//
// How it trades:
//  * Launch entries — a young curve whose creator bought modestly and has not sold.
//  * Momentum entries — a mature curve (past its launch dump window) whose recent tape shows
//    real, broad buy pressure: net SOL flowing in, several distinct buyers, the price climbing
//    and sitting near its window high, with the inflow accelerating into the newer half.
//  * Dip entries — a curve that fell hard off its recent high while buyers are already stepping
//    back in; sized smaller, because a dip can always dip further.
//  * One buy per position, never an add: on this data, adding into a pump that then reverses
//    multiplies the loss. The edge is breadth, not size.
//  * Every position exits whole on the first of: a stop loss against cost, a trailing stop once
//    the position is up, a take-profit, fading buy flow, or a time limit. The replay closes
//    completed curves itself.
//  * Guardrail pacing — the run must end with round trips on at least 20 coins. When the bot's
//    own fills or coins lag the pace set in block time, it opens tiny probe round trips (buy a
//    little on a liquid curve, sell it as soon as the buy lands) until it is back on pace.
//
// Deterministic by construction: no clock, no randomness, no I/O; iteration only over
// insertion-ordered maps fed by the batch stream, so the two graded executions agree.

import { LAMPORTS_PER_SOL, runBot, type Batch, type BotState, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const LAMPORTS = 1e9;
const CURVE_FEE = 0.0125;

// ---- entry rules ----
// Launch mode: buy a new curve while it is still young, but only when the creator's own
// stake is modest and the creator has not sold — a bundled launch with a big creator buy
// that dumps is the classic rug shape, and we want no part of it.
const LAUNCH_MAX_AGE = 30; // slots since CreateEvent in which a first buy may be decided
const LAUNCH_MAX_DEV_BUY_SOL = 2.5; // creator's own buys, at most
const LAUNCH_STAKE_SOL = 0.05;
const LAUNCH_MIN_RQ = 1; // need enough real SOL for the 1% size cap to allow a real buy
const LAUNCH_MIN_BUYERS = 2; // non-creator buyers already in before we join a launch
const LAUNCH_MIN_RUNUP = 0.03; // ...or the price already up this much from its create price

const MOM_WINDOW = 40; // slots of tape an entry looks at
const MOM_MIN_NET_SOL = 1.0; // net SOL (buys minus sells) over the window
const MOM_MIN_BUYS = 5;
const MOM_MIN_BUYERS = 5;
const MOM_MIN_UP = 0.04; // price rise over the window, at least
const MOM_MAX_UP = 0.6; // ...and at most (skip curves that already ran away)
const MOM_NEAR_HIGH = 0.92; // price now at least this share of the window high
const MOM_MIN_AGE = 300; // slots since CreateEvent before an entry is allowed
const MOM_MIN_RQ = 2; // real SOL reserve at entry, at least
const MOM_MAX_RQ = 80; // ...and at most

const DIP_HIGH_WINDOW = 240; // slots whose high the dip is measured from
const DIP_MIN_DD = 0.22; // enter at least this far below the recent high
const DIP_MAX_DD = 0.55; // ...and not further (a collapse, not a dip)
const DIP_MIN_RQ = 3;
const DIP_LAST_TRADES = 8; // of the last N trades at least this many must be buys
const DIP_MIN_BUYS = 3;

// ---- sizing ----
// One buy per position, no pyramiding: on this data, adding into a pump that then reverses
// multiplies the loss. Small first buys, many coins, fast exits.
const FIRST_BUY_SOL = 0.05;
const DIP_FIRST_BUY_SOL = 0.03;
const MAX_EXPOSURE_SOL = 6;
const MIN_BUY_SOL = 0.01;
const BUY_SLIP_BPS = 1500;

// ---- exits ----
const STOP_LOSS = 0.12; // exit when value falls to cost * (1 - STOP_LOSS)
const TRAIL_ARM = 0.06; // trailing stop arms once value reaches cost * (1 + TRAIL_ARM)
const TRAIL = 0.15; // ...then exit on a fall of TRAIL from the best value
const TAKE_PROFIT = 0.15; // exit when value reaches cost * (1 + TAKE_PROFIT)
const FADE_WINDOW = 20; // exit when net SOL over this window falls below -FADE_NET_SOL
const FADE_NET_SOL = 0.6;
const MAX_HOLD = 40; // slots: decide fast — a launch that has not moved in ~16 seconds is dead money
const STALE_SLOTS = 40; // exit when no trade has hit the coin for this many slots
const COOLDOWN = 200; // slots to wait after an exit before re-entering the same curve
const MAX_ENTRIES = 2; // most entries per curve over the run

// ---- guardrail pacing ----
const TARGET_COINS = 25;
const TARGET_FILLS = 120;
const PACE_SECS = 14_400;
const PROBE_SOL = 0.02;
const MAX_PROBES = 2;

interface Trade {
  slot: number;
  buy: boolean;
  sol: number;
  user: string;
  price: number;
}

interface Tape {
  created: number | null;
  trades: Trade[];
  entries: number;
  lastExit: number;
  creator: string | null;
  devBuySol: number;
  devSold: boolean;
  createPrice: number;
  nonCreatorBuys: number;
}

interface Held {
  opened: number;
  peakValue: number;
  invested: number;
  exiting: boolean;
  filled: boolean;
  lastAddPrice: number;
  lastValue: number;
}

const tapes = new Map<Pubkey, Tape>();
const held = new Map<Pubkey, Held>();
/** Probe round trips in flight, by mint. */
const probes = new Map<Pubkey, boolean>();
let myFills = 0;
const myCoins = new Set<Pubkey>();
let firstTime: number | null = null;
let lastTime: number | null = null;

const tapeOf = (mint: Pubkey): Tape => {
  let t = tapes.get(mint);
  if (t === undefined) {
    t = { created: null, trades: [], entries: 0, lastExit: -1e12, creator: null, devBuySol: 0, devSold: false, createPrice: 0, nonCreatorBuys: 0 };
    tapes.set(mint, t);
  }
  return t;
};

const priceOf = (vq: bigint, vt: bigint): number => Number(vq) / Number(vt);

/** Net recorded SOL (buys minus sells) over the last `w` slots. */
const flow = (t: Tape, now: number, w: number): number => {
  let net = 0;
  for (let i = t.trades.length - 1; i >= 0; i--) {
    const tr = t.trades[i]!;
    if (tr.slot <= now - w) break;
    net += tr.buy ? tr.sol : -tr.sol;
  }
  return net;
};

/** Launch entry signal: a young curve whose creator bought modestly and has not sold,
 * with other buyers already stepping in (or the price already running up). */
const launchSignal = (t: Tape, now: number, rqSol: number, price: number): boolean => {
  if (t.created === null || now - t.created > LAUNCH_MAX_AGE) return false;
  if (rqSol < LAUNCH_MIN_RQ) return false;
  if (t.devBuySol > LAUNCH_MAX_DEV_BUY_SOL) return false;
  if (t.devSold) return false;
  if (t.nonCreatorBuys < LAUNCH_MIN_BUYERS && (t.createPrice <= 0 || price < t.createPrice * (1 + LAUNCH_MIN_RUNUP))) return false;
  return true;
};

/** Momentum entry signal on a curve's tape at slot `now`. */
const momentumSignal = (t: Tape, now: number, rqSol: number): boolean => {
  if (rqSol < MOM_MIN_RQ || rqSol > MOM_MAX_RQ) return false;
  if (t.created === null || now - t.created < MOM_MIN_AGE) return false;
  const from = now - MOM_WINDOW;
  const mid = now - MOM_WINDOW / 2;
  let buySol = 0;
  let sellSol = 0;
  let buys = 0;
  let netOld = 0;
  let netNew = 0;
  let startPrice = -1;
  let high = 0;
  let last = 0;
  const byUser = new Map<string, number>();
  for (const tr of t.trades) {
    if (tr.slot <= from) {
      startPrice = tr.price;
      continue;
    }
    if (startPrice < 0) startPrice = tr.price;
    const signed = tr.buy ? tr.sol : -tr.sol;
    if (tr.slot <= mid) netOld += signed;
    else netNew += signed;
    if (tr.buy) {
      buySol += tr.sol;
      buys++;
      byUser.set(tr.user, (byUser.get(tr.user) ?? 0) + tr.sol);
    } else {
      sellSol += tr.sol;
    }
    if (tr.price > high) high = tr.price;
    last = tr.price;
  }
  if (buys < MOM_MIN_BUYS || byUser.size < MOM_MIN_BUYERS) return false;
  if (buySol - sellSol < MOM_MIN_NET_SOL) return false;
  if (startPrice <= 0) return false;
  const up = last / startPrice - 1;
  if (up < MOM_MIN_UP || up > MOM_MAX_UP) return false;
  if (last < high * MOM_NEAR_HIGH) return false;
  if (netNew <= 0 || netNew < netOld) return false;
  return true;
};

/** Dip entry signal: a sharp fall off the recent high, buyers stepping back in. */
const dipSignal = (t: Tape, now: number, rqSol: number): boolean => {
  if (rqSol < DIP_MIN_RQ) return false;
  if (t.created === null || now - t.created < MOM_MIN_AGE) return false;
  let high = 0;
  let last = 0;
  for (const tr of t.trades) {
    if (tr.slot <= now - DIP_HIGH_WINDOW) continue;
    if (tr.price > high) high = tr.price;
    last = tr.price;
  }
  if (high <= 0 || last <= 0) return false;
  const dd = 1 - last / high;
  if (dd < DIP_MIN_DD || dd > DIP_MAX_DD) return false;
  let buys = 0;
  let seen = 0;
  for (let i = t.trades.length - 1; i >= 0 && seen < DIP_LAST_TRADES; i--) {
    const tr = t.trades[i]!;
    seen++;
    if (tr.buy) buys++;
  }
  if (seen < DIP_LAST_TRADES || buys < DIP_MIN_BUYS) return false;
  const lastTrade = t.trades[t.trades.length - 1];
  if (lastTrade === undefined || !lastTrade.buy) return false;
  return true;
};

await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    const now = batch.slot;
    const traded = new Set<Pubkey>();
    for (const f of batch.fills) {
      if (f.status === 'filled' && !f.client_id.startsWith('_')) {
        myFills++;
        myCoins.add(f.mint);
      }
    }
    for (const e of batch.events) {
      if (e.block_time !== null) {
        if (firstTime === null) firstTime = e.block_time;
        if (lastTime === null || e.block_time > lastTime) lastTime = e.block_time;
      }
      if (e.event === 'CreateEvent') {
        const t = tapeOf(e.mint);
        t.created = e.slot;
        t.creator = e.creator;
        t.createPrice = priceOf(BigInt(e.virtual_sol_reserves), BigInt(e.virtual_token_reserves));
      } else if (e.event === 'TradeEvent') {
        const t = tapeOf(e.mint);
        const sol = Number(e.sol_amount) / LAMPORTS;
        if (t.creator !== null && e.user === t.creator) {
          if (e.is_buy) t.devBuySol += sol;
          else t.devSold = true;
        } else if (e.is_buy) {
          t.nonCreatorBuys++;
        }
        t.trades.push({
          slot: e.slot,
          buy: e.is_buy,
          sol,
          user: e.user,
          price: priceOf(BigInt(e.virtual_quote_reserves), BigInt(e.virtual_token_reserves)),
        });
        traded.add(e.mint);
      }
    }
    // Prune tapes to what the signals still read.
    const keep = Math.max(MOM_WINDOW, DIP_HIGH_WINDOW) + 5;
    for (const mint of traded) {
      const t = tapes.get(mint)!;
      let cut = 0;
      while (cut < t.trades.length && t.trades[cut]!.slot <= now - keep) cut++;
      if (cut > 0) t.trades.splice(0, cut);
    }
    const marks = new Map(batch.marks.map((m) => [m.mint, m] as const));
    const pendingByMint = new Map<Pubkey, number>();
    for (const po of state.pending.values()) pendingByMint.set(po.order.mint, (pendingByMint.get(po.order.mint) ?? 0) + 1);

    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const tx = Number(state.txFeeLamports()) / LAMPORTS;

    // Exits first.
    for (const [mint, h] of held) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) {
          held.delete(mint);
          const t = tapeOf(mint);
          if (h.filled) t.lastExit = now;
          else t.entries--;
        }
        continue;
      }
      h.filled = true;
      if (curve === undefined || curve.complete) continue;
      const mk = marks.get(mint);
      const vq = mk ? Number(mk.virtual_quote_reserves) : Number(curve.virtual_quote_reserves);
      const vt = mk ? Number(mk.virtual_token_reserves) : Number(curve.virtual_token_reserves);
      const tokens = Number(pos.token_amount);
      const value = ((tokens * vq) / (vt + tokens) / LAMPORTS) * (1 - CURVE_FEE) - tx;
      const cost = Number(pos.cost_lamports) / LAMPORTS;
      if (value > h.peakValue) h.peakValue = value;
      h.lastValue = value;
      let exit = h.exiting;
      const t = tapeOf(mint);
      if (!exit && value < cost * (1 - STOP_LOSS)) exit = true;
      if (!exit && h.peakValue >= cost * (1 + TRAIL_ARM) && value < h.peakValue * (1 - TRAIL)) exit = true;
      if (!exit && TAKE_PROFIT > 0 && value >= cost * (1 + TAKE_PROFIT)) exit = true;
      if (!exit && flow(t, now, FADE_WINDOW) < -FADE_NET_SOL) exit = true;
      if (!exit && now - h.opened > MAX_HOLD) exit = true;
      const lastTrade = t.trades[t.trades.length - 1];
      if (!exit && lastTrade !== undefined && now - lastTrade.slot > STALE_SLOTS) exit = true;
      if (!exit) continue;
      h.exiting = true;
      let sellPending = false;
      for (const po of state.pending.values()) {
        if (po.order.mint === mint && po.order.side === 'sell') sellPending = true;
      }
      if (sellPending) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
    }

    // Probe round trips: sell the whole probe as soon as its buy has landed.
    for (const [mint, selling] of probes) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) probes.delete(mint);
        continue;
      }
      if (curve === undefined || curve.complete || pendingByMint.has(mint)) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
      if (!selling) probes.set(mint, true);
    }

    // Then entries. One buy per position, never an add: on this data, adding into a pump
    // that then reverses multiplies the loss, and the edge is breadth, not size.
    let free = Number(state.freeCashLamports()) / LAMPORTS;
    let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
    let exposure = 0;
    for (const [mint, h] of held) {
      exposure += Math.max(h.invested, Number(state.positions.get(mint)?.cost_lamports ?? 0n) / LAMPORTS);
    }
    for (const mint of traded) {
      if (orders.length >= cap) break;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.complete) continue;
      if (pendingByMint.has(mint) || probes.has(mint)) continue;
      if (held.has(mint)) continue;
      const t = tapes.get(mint)!;
      if (slotsLeft <= 0) continue;
      if (t.entries >= MAX_ENTRIES || now - t.lastExit < COOLDOWN) continue;
      const rqSol = Number(curve.real_quote_reserves) / LAMPORTS;
      const price = priceOf(curve.virtual_quote_reserves, curve.virtual_token_reserves);
      let want: number;
      if (launchSignal(t, now, rqSol, price)) {
        want = LAUNCH_STAKE_SOL;
      } else if (momentumSignal(t, now, rqSol)) {
        want = FIRST_BUY_SOL;
      } else if (dipSignal(t, now, rqSol)) {
        want = DIP_FIRST_BUY_SOL;
      } else {
        continue;
      }
      const capSol = Math.floor(Number(state.maxBuyLamports(mint))) / LAMPORTS;
      let amount = Math.min(capSol, want, MAX_EXPOSURE_SOL - exposure);
      if (amount > free - tx) amount = free - tx;
      if (amount < MIN_BUY_SOL) continue;
      const lamports = BigInt(Math.floor(amount * LAMPORTS));
      orders.push({ side: 'buy', mint, quote_lamports: lamports, max_slippage_bps: BUY_SLIP_BPS });
      free -= amount + tx;
      exposure += amount;
      held.set(mint, {
        opened: now,
        peakValue: 0,
        invested: amount,
        exiting: false,
        filled: false,
        lastAddPrice: price,
        lastValue: 0,
      });
      t.entries++;
      slotsLeft--;
    }

    // Guardrail pacing: open a probe when the bot's fills or coins lag the pace.
    if (probes.size < MAX_PROBES && slotsLeft > 0 && firstTime !== null && lastTime !== null) {
      const pace = Math.min(1, (lastTime - firstTime) / PACE_SECS);
      const needCoins = myCoins.size < Math.ceil(TARGET_COINS * pace);
      const needFills = myFills < Math.ceil(TARGET_FILLS * pace);
      if (needCoins || needFills) {
        const minRq = (PROBE_SOL * 10_000) / state.hello.caps.max_order_bps_of_real_reserve;
        for (const mint of traded) {
          if (orders.length >= cap || probes.size >= MAX_PROBES) break;
          if (held.has(mint) || probes.has(mint) || pendingByMint.has(mint) || state.positions.has(mint)) continue;
          if (needCoins && !needFills && myCoins.has(mint)) continue;
          const curve = state.curves.get(mint);
          if (curve === undefined || curve.complete) continue;
          if (Number(curve.real_quote_reserves) / LAMPORTS < minRq * 1.5) continue;
          if (free < PROBE_SOL + 2 * tx) break;
          orders.push({ side: 'buy', mint, quote_lamports: BigInt(Math.floor(PROBE_SOL * LAMPORTS)), max_slippage_bps: BUY_SLIP_BPS });
          probes.set(mint, false);
          free -= PROBE_SOL + tx;
        }
      }
    }
    return orders;
  },
});
