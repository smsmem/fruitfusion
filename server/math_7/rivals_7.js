'use strict';
// rivals_7.js — math_7 Rival board (MATH_SPEC_7 delta on MATH_SPEC_6): NLS start (S76), y-roles (S77), bonus trigger k <= 2 and r_m - k >= 7 (S78), late cap + guard (S80), N1 audit.
// (history) rivals_4.js — math_4 Rival board (MATH_SPEC_4 + errata E1, E2, N-R1). A PURE function of (streams, rating, bot, the player event trace, lookahead results).
// Bank-quantile-conditioned targets (tiltlib.js), S_lo* running-max lower bound, late lookahead at drops 16/17/18 (+ bonus 19-21), board = payout,
// bonus trigger at the mark, alerts before the mark only. runBoard() re-derives the whole board from the trace (server replay = harness = same code).
// Prefix property: runBoard(upto=t) equals the first t ticks of runBoard(full) (the bonus check relies on it).
const KL = require('./kernlib.js');
const FRUITS = ['Peach', 'Plum', 'Cherry', 'Berry', 'Melon', 'Mango', 'Kiwi', 'Lime', 'Lemon', 'Grape', 'Pear', 'Fig', 'Apple', 'Guava', 'Papaya', 'Lychee'];
const PARTS = ['Pit', 'Pip', 'Seed', 'Peel', 'Rind', 'Zest', 'Stem', 'Leaf', 'Juice', 'Drop', 'Pop', 'Bloom', 'Slice', 'Core', 'Twist'];
const HANDLE_RE = /^(Peach|Plum|Cherry|Berry|Melon|Mango|Kiwi|Lime|Lemon|Grape|Pear|Fig|Apple|Guava|Papaya|Lychee)(Pit|Pip|Seed|Peel|Rind|Zest|Stem|Leaf|Juice|Drop|Pop|Bloom|Slice|Core|Twist)_[1-9][0-9]$/;
const f20 = v => Math.floor(v / 20) * 20, c20 = v => Math.ceil(v / 20) * 20, f5 = KL.f5, c5 = KL.c5;
const mDn = (cfg, S) => Math.max(cfg.board.mDn.frac * S, cfg.board.mDn.abs);
const mUp = (cfg, S) => Math.max(cfg.board.mUp.frac * S, cfg.board.mUp.abs);

function tap(s, name, log, cur) { // counts reads with the tick they happened at
  return { float() { log[name].push(cur.t); return s.float(); }, gauss() { log[name].push(cur.t); return s.gauss(); }, int(n) { log[name].push(cur.t); return s.int(n); } };
}

// per bot reference context: sorted bank finals + the fitted kernel rows (cached)
const CTX = new Map();
function getCtx(par) {
  const cfg = par.cfg, B = cfg.board;
  const key = [par.bot, B.thinCap, B.mUp.frac, B.mUp.abs, B.mDn.frac, B.mDn.abs, par.kern && par.kern.sha].join('|');
  let c = CTX.get(key);
  if (!c) {
    const X = par.bank.ref.classic[par.bot]; if (!X) throw new Error('no bank reference for bot ' + par.bot);
    c = KL.makeCtx(X, par.kern.bots[par.bot], s => mUp(cfg, s), s => mDn(cfg, s), { thinCap: B.thinCap });
    CTX.set(key, c);
  }
  return c;
}

// par: {cfg, bank, kern, bot, place (null ok before the mark), rating}
// S: {board, rival, alert} fresh Xo streams. tr: {Pt[], Ht[], TB[], dropTicks[], tMark|null, looks[{t,n,S,final}]}. upto: last tick to process (non-final run).
// fin (final run): {Sfinal, tEnd, overflow, lastDropT}
function runBoard(par, S, tr, upto, fin) {
  const cfg = par.cfg, B = cfg.board, k = par.place;
  const nDrops = cfg.rules.classic.drops;
  const rd = { board: [], rival: [], alert: [] }, cur = { t: -1 };
  const sb = tap(S.board, 'board', rd, cur), sr = tap(S.rival, 'rival', rd, cur), sa = tap(S.alert, 'alert', rd, cur);
  const W5 = par.bank.w5.classic, gArr = par.bank.g.classic;
  const rpace = par.rating; // kappa = 1 (U1)
  // ---------- init (tick -1): board stream = handles, a_i, first gaps; alert stream = count, times, designated Rivals
  const riv = [], used = new Set();
  for (let i = 0; i < B.rivals; i++) {
    let h, f, p, nn;
    do { f = sb.int(FRUITS.length); p = sb.int(PARTS.length); nn = 10 + sb.int(90); h = FRUITS[f] + PARTS[p] + '_' + nn; } while (used.has(h));
    used.add(h);
    riv.push({ i, handle: h, icon: FRUITS[f].toLowerCase(), a: 0, R: 0, nextEv: 0, lastEv: -1e9, evs: [], drops: 0, leader: false, set: null, tau: 0, v: 0, w: 0, z: 0, frozen: false, frozenAtMark: false, frozenEver: false, desig: -1, recent: [], settles: 0 });
  }
  for (const r of riv) r.a = Math.min(B.aClamp[1], Math.max(B.aClamp[0], Math.exp(B.aSigma * sb.gauss())));
  const gapDraw = (s) => B.gapBase + Math.round(B.gapMedian * Math.exp(B.gapSigma * s.gauss()));
  for (const r of riv) r.nextEv = gapDraw(sb);
  for (const r of riv) r.slack = B.slackMax * sb.float(); // tie-breaker (U3)
  const byA = riv.slice().sort((x, y) => y.a - x.a || x.i - y.i); // highest a first
  // S76 (NLS): u_L then l_1..l_9 from `board` (the same 10 reads in every round); L ~ W_L (the natural place-at-30% law); leaders = the L Rivals with the highest a (ties by index)
  const uL = sb.float(); for (const r of riv) r.ell = sb.float();
  const WL = B.start.WL, WLt = WL.reduce((a, b) => a + b, 0); let Lc = 0, accL = 0; { const xL = uL * WLt; for (; Lc < WL.length - 1; Lc++) { accL += WL[Lc]; if (xL < accL) break; } }
  const Ln = Lc; for (let j = 0; j < Ln; j++) byA[j].leader = true;
  const nonLeaders = riv.filter(r => !r.leader);
  // alerts (pre-mark only, S56): count, times phi ~ U(0.15, 0.30), designated non-leaders
  const ua = sa.float(); const nAl = ua < B.alert.probs[0] ? 0 : ua < B.alert.probs[0] + B.alert.probs[1] ? 1 : 2;
  const alerts = [];
  const alTimes = []; for (let j = 0; j < nAl; j++) alTimes.push(B.alert.lo + (B.alert.hi - B.alert.lo) * sa.float());
  alTimes.sort((x, y) => x - y);
  const pool = nonLeaders.slice(); const perm = [];
  while (pool.length) perm.push(pool.splice(sa.int(pool.length), 1)[0]);
  for (let j = 0; j < Math.min(nAl, perm.length); j++) { alerts.push({ j, phi: alTimes[j], rival: perm[j].i, state: 'pending', t: null }); perm[j].desig = j; }
  // ---------- helpers
  const Pt = tr.Pt, Ht = tr.Ht, TBr = tr.TB, dts = tr.dropTicks;
  const looks = tr.looks || [];
  let lkPtr = -1;
  const tMarkEff = tr.tMark !== null && tr.tMark !== undefined ? tr.tMark : (fin ? fin.tEnd : Infinity);
  const tClose = fin ? fin.tEnd + (fin.overflow ? B.playoutTicks : B.closeTicksClassic) : upto;
  const stop = fin ? tClose : upto;
  let dptr = 0, sloStar = 0;
  const capStat = { climbs: 0, bites: 0 }, guardStat = { steps: 0, fails: 0 };
  const Pof = t => { if (fin && t >= fin.tEnd) return fin.Sfinal; const i = t < Pt.length ? t : Pt.length - 1; return i < 0 ? 0 : Pt[i]; };
  const phiOf = t => (fin && t >= fin.tEnd) ? 1 : Math.min(1, dptr / nDrops);
  const gOf = t => (fin && t >= fin.tEnd) ? 1 : gArr[Math.min(dptr, nDrops)];
  const Rat = (r, t) => { let v = 0; for (let e = r.evs.length - 1; e >= 0; e--) if (r.evs[e].t <= t) { v = r.evs[e].after; break; } return v; };
  const sloArr = new Int32Array(stop + 1);
  const events = [];
  let markDone = false, markInfo = null, ctx = null;
  const ctxOf = () => ctx || (ctx = getCtx(par));
  let Tg = null;

  const doMark = t => {
    markDone = true; cur.t = t;
    const Pm = Pof(t), Rm = riv.map(r => r.R);
    let rank = 1; for (const r of riv) if (r.R > Pm) rank++;
    // fixed read order at the mark (MATH_SPEC_7 3.3 step 6): v_1..v_9, w_1..w_9, z_1..z_9, e, s, h, y_1..y_9, then the tau reads. The same reads in every round whatever the draw.
    const idx0 = rd.rival.length;
    for (const r of riv) r.v = sr.float();
    for (const r of riv) r.w = sr.float();
    for (const r of riv) r.z = sr.float();
    const e = sr.float(), sCoin = sr.float(), h = sr.float();
    for (const r of riv) r.y = sr.float();
    const idx1 = rd.rival.length;
    // roles (S77): A = the k-1 Rivals with the smallest y (ties by index), B = the rest. Roles read no a, no R_m and no v.
    let A = [];
    if (k !== null && k !== undefined) A = riv.slice().sort((x, y) => x.y - y.y || x.i - y.i).slice(0, k - 1);
    for (const r of riv) r.set = 'B';
    for (const r of A) r.set = 'A';
    for (const a of alerts) if (a.state === 'pending') { a.state = 'abandoned'; a.t = t; } // give-up at the mark (S56)
    // close-finish flag (S57): one per round, the same rate at every place; side: 1st always down, last always up, otherwise a fair coin
    const nPlaces = B.places;
    const close = e < B.closeRate;
    const sideUp = (k === 1) ? false : (k === nPlaces) ? true : sCoin < 0.5;
    const closeSide = close && k !== null && k !== undefined ? (sideUp ? 'up' : 'dn') : null;
    // sides (S77): within each side the Rivals are taken in ascending y: the first is the close Rival (if that side is flagged), the next the neighbour, the rest the others
    const sideSpec = (set, isA) => {
      const ord = set.slice().sort((x, y) => x.y - y.y || x.i - y.i);
      const nAll = ord.length; let closeI = -1;
      if (closeSide === (isA ? 'up' : 'dn') && ord.length) closeI = ord.shift().i;
      const nb = ord.length ? ord.shift() : null;
      const nN = nAll - (closeI >= 0 ? 1 : 0), nOth = ord.length;
      const others = ord.slice().sort((x, y) => x.z - y.z || x.i - y.i).map((r, q) => ({ i: r.i, sigma: q + 1, vp: (q + r.v) / nOth, w: r.w, z: r.z }));
      others.sort((x, y) => x.vp - y.vp || x.i - y.i); // chain order: ascending v'
      return { close: closeI, nb: nb ? nb.i : -1, vnb: nb ? nb.v : 0, nN, others };
    };
    const specA = sideSpec(A, true), specB = sideSpec(riv.filter(r => r.set === 'B'), false);
    Tg = new KL.Targets(ctxOf(), { h, A: specA, B: specB });
    // tau reads (A-Rivals in index order), after the fixed block
    const phim = Math.min(1, dptr / nDrops);
    const lo = phim + B.tauLoOffset;
    for (const r of riv) if (r.set === 'A') r.tau = lo + (B.tauHi - lo) * sr.float();
    for (const r of riv) if (r.set === 'B' && r.R > Math.max(0, f20((B.bCap - r.slack) * Pm - B.bOff))) { r.frozen = true; r.frozenAtMark = true; r.frozenEver = true; }
    // bonus trigger (S78): a win draw at 1st or 2nd that sits >= d_b places behind its drawn place at the mark: k <= 2 and r_m - k >= d_b. Deterministic, no stream.
    const bonus = (k !== null && k !== undefined && k <= B.bonus.kMax) && (rank - k >= B.bonus.db);
    markInfo = { t, Pm, rank, Rm, A: A.map(r => r.i), frozen: riv.filter(r => r.frozenAtMark).map(r => r.i), phi: phim, bonus, vStart: idx0, vReads: idx1 - idx0, v: riv.map(r => r.v), w: riv.map(r => r.w), z: riv.map(r => r.z), y: riv.map(r => r.y), L: Ln, leaders: riv.filter(r => r.leader).map(r => r.i),
      flag: { close, side: closeSide, e, s: sCoin, h }, roles: { A: specA, B: specB }, nbLeaderA: specA.nb >= 0 ? (riv[specA.nb].leader ? 1 : 0) : -1 };
  };

  const windowRem = (r, t) => { let s = 0; for (const e of r.recent) if (e[0] > t - B.windowTicks) s += e[1]; return Math.max(0, f5(W5 - s)); };
  const apply = (r, t, target, post, settleOK) => { // move R toward target, capped by step and 5 s window. Pre-mark steps are multiples of 20; from the mark on multiples of 5 and >= minStep (a final settle may be smaller, only when it completes the target)
    const gain = target - r.R; if (gain <= 0) return;
    const avail = Math.min(B.sCap - r.evStep, windowRem(r, t), gain);
    let step = post ? f5(avail) : f20(avail);
    if (post && avail < gain) { // cap-limited climb: shave a deterministic 0-15 (a function of the tick and the Rival, no stream) so residues mod 20 appear during the climb, not only on the last event (N5)
      const d = 5 * ((Math.floor(t / 5) + 3 * r.i) % 4); if (step - d >= B.minStep) step -= d;
    }
    if (post && step < B.minStep) {
      if (settleOK && gain < B.minStep && f5(gain) <= Math.min(B.sCap - r.evStep, windowRem(r, t)) && f5(gain) > 0) { step = f5(gain); r.settles++; } else return;
    }
    if (step <= 0) return;
    r.R += step; r.evStep += step; r.recent.push([t, step]);
  };

  const processEvent = (r, t) => {
    cur.t = t;
    const post = t >= tMarkEff;
    const lk = lkPtr >= 0 ? looks[lkPtr] : null;
    const Pn = Pof(t), phi = phiOf(t);
    const late = dptr >= B.lookFromDrop || lk !== null; // from the release of drop 16 (or a lookahead exists, e.g. after an overflow)
    const before = r.R; r.evStep = 0;
    let lift = false;
    // next event time
    if (!post) r.nextEv = t + gapDraw(sb);
    else if (r.set === 'A' && late) r.nextEv = (lk && lk.final) ? t + B.finalGapCap : Infinity; // A-Rivals move only at lookahead ticks and in the closing window
    else r.nextEv = t + Math.min(gapDraw(sr), late ? B.finalGapCap : 1e9);
    const pace = f20(rpace * r.a * gOf(t));
    const al = r.desig >= 0 ? alerts[r.desig] : null;
    const alActive = al && al.state === 'pending' && !post;
    let cap, target;
    if (!post) {
      if (r.leader) { // S76: a leader sits in [P + 20, 1.25 P + 100]: min(cap_hi, max(pace, floor_i)); cap_hi = f20(1.25 P) + 100 while the jar height Ht(t) < hGate, else f20(0.90 P)
        const Hh = Ht[t] === undefined ? 1 : Ht[t]; cap = Hh < B.hGate ? f20(B.leaderL * Pn) + B.leaderF : f20(B.nonLeaderCap * Pn);
        const fl = c20(Pn + B.start.band.off + r.ell * (B.start.band.frac * Pn + B.start.band.abs));
        target = Math.min(cap, Math.max(pace, fl));
      } else { cap = f20((B.nonLeaderCap - r.slack) * Pn); target = Math.min(pace, cap); }
    } else {
      const inWin = !!(fin && t >= fin.tEnd);
      const g = gOf(t), Slo = sloStar, TF = S0 => Tg.val(r.i, S0);
      let Sproj = Math.max(Slo, Pn); if (lk) Sproj = Math.max(Sproj, lk.S);
      if (!inWin && g > 0 && dptr >= B.gCurveFrom) Sproj = Math.max(Sproj, Pn / g);
      if (r.set === 'B') {
        const Bcap = Math.max(0, f20((B.bCap - r.slack) * Pn - B.bOff));
        if (r.R > Bcap) {
          cap = Bcap; r.frozen = true; r.frozenEver = true; target = r.R;
          if (lk && lk.final && r.R >= lk.S) { target = Math.max(r.R, c5(lk.S + mUp(cfg, lk.S))); lift = true; } // S52: lift a frozen Rival that ends above the player to the m_up gap
        } else {
          r.frozen = false;
          const tb = (late || inWin) ? TF(Slo) : Math.min(TF(Slo), f5(TF(Sproj) * g));
          cap = inWin ? tb : Bcap; // in the finishing window the B-cap becomes the Rival's own target (MATH_SPEC_5 1.1)
          target = Math.min(tb, cap);
        }
      } else if (late) { // A, lookahead regime: move toward T_i(S_look) (a projection), never below the true bound
        const tFull = TF(Math.max(lk ? lk.S : 0, Slo));
        if (lk && lk.final) target = tFull; // the exact final look: the Rival climbs the rest
        else { // S80: a non-final lookahead climb stops at T_i(S_lo*) + O(S_lo*), O(x) = max(0.5 x, 500)
          const capLvl = f5(TF(Slo) + Math.max(B.late.O.frac * Slo, B.late.O.abs));
          if (tFull > r.R) { capStat.climbs++; if (tFull > capLvl) capStat.bites++; }
          target = Math.min(tFull, capLvl);
        }
        cap = target;
      } else if (phi >= r.tau) { target = Math.min(TF(Slo), f5(TF(Sproj) * g)); cap = target; }
      else { cap = f5(0.97 * Pn); target = Math.min(f5(TF(Sproj) * g), cap); if (r.R > cap) target = r.R; }
    }
    // closing window: no two Rivals (and no Rival and the player) may end on the same score (J1). An overshooting Rival cannot come down, so a Rival steps up by 5s to the first value that no FINAL Rival holds
    // (a Rival is final when this was its last event in the window). Every mover looks at the others' current scores, so a move never creates a tie, and the last mover resolves it.
    let bump = false;
    if (post && fin && t >= fin.tEnd) {
      const tv0 = Math.max(target, r.R); let tv = tv0;
      const clash = v => v === fin.Sfinal || riv.some(o => o !== r && o.R === v && o.nextEv > tClose);
      while (clash(tv)) tv += 5;
      if (tv !== tv0) { target = tv; bump = true; }
    }
    // alert designated Rival: lags at preCap*P until its alert has fired (before the mark only)
    if (alActive) target = Math.min(target, Math.max(f20(B.alert.preCap * Pn), r.R));
    apply(r, t, target, post, !!((lk && lk.final) || (fin && t >= fin.tEnd)));
    // ----- alert delivery (truthfulness enforced here and audited independently)
    if (alActive && al.state === 'pending' && phi >= al.phi) {
      const prev = r.desig > 0 ? alerts[r.desig - 1] : null;
      const spaced = !prev || prev.state !== 'fired' || t - prev.t >= B.alert.minGapTicks;
      if (spaced && Pn > 0) {
        const tp = Math.max(0, t - B.alert.lookbackTicks);
        const gapPrev = Pof(tp) - Rat(r, tp);
        const needGap = Math.min(Math.max(B.alert.within * Pn, B.alert.withinFloor), (1 - B.alert.closeFrac) * gapPrev);
        const Rneed = c20(Pn - needGap);
        const capNow = Math.min(Math.max(cap, 0) + B.slackMax * 2 * Pn, Math.max(0, f20(B.bCap * Pn - B.bOff)), f20(B.nonLeaderCap * Pn)); // same test for every rung (pre-mark only)
        if (gapPrev > 0 && Rneed <= capNow && Rneed < Pn) {
          if (Rneed > r.R) apply(r, t, Rneed, false, false);
          const gapNow = Pn - r.R;
          if (r.R < Pn && gapNow <= Math.max(B.alert.within * Pn, B.alert.withinFloor) + 1e-9 && gapNow <= (1 - B.alert.closeFrac) * gapPrev + 1e-9) { al.state = 'fired'; al.t = t; al.gapPrev = gapPrev; al.gapNow = gapNow; al.P = Pn; al.R = r.R; }
        }
      }
    }
    r.lastEv = t;
    if (r.R !== before) r.drops++;
    events.push({ t, i: r.i, before, after: r.R, P: Pn, post, lift, set: r.set, bump });
    r.evs.push({ t, before, after: r.R });
  };

  // S80 guard (rev 1 / N1): from the drop-16 lookahead tick until t_End an A-Rival below its guard level G_i(t) steps up to it (spacing and the 5 s window respected, step may be < 20). It never moves a B-Rival.
  // G_i(t) = c5(P + m_up(P)) (non-close A-Rivals); the flagged close-up Rival: c5(P + 20 + h (m_up(P) - 20)) with its own mark-time h.
  const guardTry = (r, t) => {
    const Pn = Pof(t), mu = mUp(cfg, Pn), gl = B.late.guardLead;
    const G = (markInfo.roles.A.close === r.i) ? c5(Pn + gl + markInfo.flag.h * (mu - gl)) : c5(Pn + mu);
    if (r.R >= G) { r.gfail = false; return; }
    const before = r.R; r.evStep = 0;
    apply(r, t, G, true, true);
    const failNow = r.R < G; if (failNow && !r.gfail) guardStat.fails++; r.gfail = failNow; // one failure per episode (window exhausted / step under the minimum)
    if (r.R === before) return;
    r.gT = t; r.drops++; guardStat.steps++; r.gsteps = (r.gsteps || 0) + 1; // U-choice: a guard event is "an event that tick" (spec 4.4 (2)) and is not subject to the 30-tick spacing of scheduled events; r.lastEv (the spacing clock) is not touched
    events.push({ t, i: r.i, before, after: r.R, P: Pn, post: true, lift: false, set: 'A', bump: false, guard: true });
    r.evs.push({ t, before, after: r.R });
  };
  // ---------- main loop
  let sloFallbacks = 0;
  for (let t = 0; t <= stop; t++) {
    cur.t = t;
    while (dptr < dts.length && dts[dptr] <= t) dptr++;
    let sl;
    if (fin && t >= fin.tEnd) sl = fin.Sfinal; else if (t < Pt.length) sl = Pt[t] + Math.floor(B.sloFrac * (TBr ? (TBr[t] || 0) : 0)); else sl = 0;
    if (sl > sloStar) sloStar = sl;
    sloArr[t] = sloStar;
    let arrived = false;
    while (lkPtr + 1 < looks.length && looks[lkPtr + 1].t <= t) { lkPtr++; arrived = true; }
    if (!markDone && t >= tMarkEff) doMark(t);
    if (arrived) for (const r of riv) if (r.set === 'A') r.nextEv = Math.max(t, r.lastEv + B.minSpacing);
    for (const r of riv) if (r.nextEv === t) processEvent(r, t);
    if (markDone && lkPtr >= 0 && !(fin && t >= fin.tEnd)) for (const r of riv) if (r.set === 'A' && r.gT !== t) guardTry(r, t);
  }
  if (!markDone && fin) doMark(Math.min(stop, tMarkEff === Infinity ? stop : tMarkEff));
  // ---------- outputs
  const len = stop + 1;
  const Rt = riv.map(r => { const a = new Int32Array(len); let v = 0, e = 0; for (let t = 0; t < len; t++) { while (e < r.evs.length && r.evs[e].t <= t) { v = r.evs[e].after; e++; } a[t] = v; } return a; });
  return { riv, alerts, events, Rt, markInfo, tMarkEff, tClose: stop, reads: rd, Pof, looks, sloArr, sloFallbacks, par: { place: k }, ctx, Tg, L: Ln, capStat, guardStat };
}

const med = a => { if (!a.length) return -1; const s = a.slice().sort((x, y) => x - y); return s[Math.floor(s.length / 2)]; };
// ---------- evaluation of a finished round (fin given): shown place (= paid place), margins (neighbours only), wrong places, ties, close finishes, feel stats
function evaluate(cfg, brd, tr, fin, k, round) {
  const B0 = cfg.board;
  const riv = brd.riv, S = fin.Sfinal, finalR = riv.map(r => r.R);
  const shown = 1 + finalR.filter(v => v >= S).length;
  const wrongDown = shown > k ? 1 : 0, wrongUp = shown < k ? 1 : 0;
  const mu = mUp(cfg, S), md = mDn(cfg, S);
  let upI = -1, dnI = -1;
  for (const r of riv) { if (r.R >= S) { if (upI < 0 || r.R < riv[upI].R) upI = r.i; } else if (dnI < 0 || r.R > riv[dnI].R) dnI = r.i; }
  const gapUp = upI >= 0 ? riv[upI].R - S : null, gapDn = dnI >= 0 ? S - riv[dnI].R : null;
  // S45: a B-Rival that was frozen and sits ABOVE its own target at the end (it cannot be lowered) and finishes within m_dn below the player: shown = drawn, counted as wrong (MATH_SPEC_4 S45)
  const stuck = r => r.set === 'B' && r.frozenEver && brd.Tg && r.R > brd.Tg.val(r.i, S);
  let wrongS45 = 0; for (const r of riv) if (r.R < S && S - r.R < md && stuck(r)) wrongS45 = 1;
  const flag = brd.markInfo && brd.markInfo.flag ? brd.markInfo.flag.side : null;
  const cuMeas = gapUp !== null && gapUp < mu ? 1 : 0, cdMeas = gapDn !== null && gapDn < md ? 1 : 0;
  // margin violation (MATH_SPEC_5 1.4): a non-flagged neighbour under its margin (S45 frozen-B shortfalls excepted), any neighbour gap under 20 (K4 floor), any tie
  const violUp = cuMeas && flag !== 'up' ? 1 : 0;
  const violDn = cdMeas && flag !== 'dn' && !stuck(riv[dnI]) ? 1 : 0;
  const floorBreak = ((gapUp !== null && gapUp < 20) || (gapDn !== null && gapDn < 20)) ? 1 : 0;
  let ties = 0; { const all = finalR.concat([S]).sort((x, y) => x - y); for (let i = 1; i < all.length; i++) if (all[i] === all[i - 1]) ties++; }
  const wrong = wrongDown || wrongUp || wrongS45 ? 1 : 0;
  // J3 bunching: all k-1 >= 2 Rivals above lie within span <= max(0.02 S, 40)
  const above = finalR.filter(v => v >= S); let bunch = -1;
  if (above.length >= 2) bunch = (Math.max(...above) - Math.min(...above)) <= Math.max(0.02 * S, 40) ? 1 : 0;
  // lead changes + player place moves, per tick over the player's round (player is index -1, wins ties)
  const tEnd = fin.tEnd, Pof = brd.Pof, Rt = brd.Rt;
  const tM = brd.markInfo ? brd.markInfo.t : tEnd;
  let leader = -1, leadChanges = 0, prevPl = 1, mvUpPre = 0, mvDnPre = 0, mvUpPost = 0, mvDnPost = 0, lastUpT = -1;
  const lim = Math.min(tEnd, brd.tClose);
  for (let t = 0; t <= lim; t++) {
    const P = Pof(t); let best = -1, bv = P, pl = 1;
    for (let i = 0; i < Rt.length; i++) { const v = Rt[i][t]; if (v > bv) { bv = v; best = i; } if (v > P) pl++; }
    if (t > 0 && best !== leader) leadChanges++;
    leader = best;
    if (t > 0 && pl !== prevPl) { if (pl < prevPl) { if (t < tM) mvUpPre++; else { mvUpPost++; lastUpT = t; } } else { if (t < tM) mvDnPre++; else mvDnPost++; } }
    prevPl = pl;
  }
  const dts = tr.dropTicks, nD = cfg.rules.classic.drops;
  const phiAt = t => { if (t >= tEnd) return 1; let n = 0; while (n < dts.length && dts[n] <= t) n++; return Math.min(1, n / nD); };
  let latePass = 0, latePassVis = 0, passes = 0, lastPassPhi = null;
  const big = [];
  for (const e of brd.events) {
    if (e.after > e.before) {
      if (e.after >= e.before + 1000) big.push(e.t);
      const P = Pof(e.t);
      if (e.before <= P && e.after > P) { passes++; const ph = phiAt(e.t); lastPassPhi = ph; if (ph >= 0.9) { latePass++; if (e.before <= Pof(Math.max(0, e.t - 1))) latePassVis++; } } // latePassVis: the Rival was already behind the player on the previous tick (what the one-tick-lagged strip could show)
    }
  }
  let latePlCross = 0;
  for (const r of riv) if (r.set === 'A') { const R = Rt[r.i]; for (let t = 1; t <= lim; t++) { if (R[t - 1] >= Pof(t - 1) && Pof(t) > R[t] && phiAt(t) >= 0.9) latePlCross++; } }
  let relN = 0, relEv = 0, relEvNG = 0; const relSteps = [];
  for (let n = 16; n <= dts.length; n++) {
    relN++; const t = dts[n - 1]; let hit = false, hitNG = false;
    for (const e of brd.events) if (e.t === t && e.set === 'A' && e.after > e.before) { hit = true; if (!e.guard) hitNG = true; relSteps.push(e.after - e.before); }
    if (hit) relEv++; if (hitNG) relEvNG++;
  }
  // minimum visible gap to the Rival just above from the drop-16 release on (N1 report); the player's last up-move; the longest flat stretch of a B-Rival that was ahead at the mark (R10)
  let minGapAbove = -1;
  if (dts.length >= 16) { let mg = Infinity; for (let t = dts[15]; t <= lim; t++) { const P = Pof(t); for (let i = 0; i < Rt.length; i++) { const v = Rt[i][t]; if (v > P && v - P < mg) mg = v - P; } } minGapAbove = isFinite(mg) ? mg : -1; }
  let stall = -1; if (brd.markInfo) for (const r of riv) if (r.set === 'B' && brd.markInfo.Rm[r.i] > brd.markInfo.Pm) { const e1 = r.evs.find(e => e.t >= tM && e.after > e.before); stall = Math.max(stall, (e1 ? e1.t : tEnd) - tM); }
  let nBig = 0, nFol = 0;
  for (const m of round.merges) if (m.pts >= 1000) { nBig++; if (big.some(tt => tt > m.t && tt <= m.t + 60)) nFol++; }
  const covered = new Uint8Array(tEnd + 1); for (const tt of big) for (let t = Math.max(0, tt - 60); t < tt && t <= tEnd; t++) covered[t] = 1;
  let cov = 0; for (let t = 0; t <= tEnd; t++) cov += covered[t];
  // overshoot / undershoot of the A-Rivals against T_i(S_final), thin-tail shares, running-max share
  const Ocap = x => Math.max(cfg.board.late.O.frac * x, cfg.board.late.O.abs); let capViol = 0;
  let nOver = 0, maxOver = 0, nUnder = 0, thinAn = 0, nA = 0, thinBn = 0, nB = 0, rmaxN = 0, rmaxDen = 0;
  if (brd.ctx && brd.Tg) {
    const c = brd.ctx, Tg = brd.Tg;
    const tA = c.N - KLlb(c.X, S + c.mUp(S)) <= 0, tB = KLub(c.X, S - c.mDn(S)) <= 0;
    for (const r of riv) {
      if (Tg.side[r.i] === undefined) continue;
      rmaxDen++; if (Tg.val(r.i, S) > Tg.raw(r.i, S)) rmaxN++;
      if (r.set === 'A') { nA++; if (tA) thinAn++; const T = Tg.val(r.i, S); if (r.R > T) { nOver++; maxOver = Math.max(maxOver, r.R - T); if (r.R - T > Ocap(S) + 45) capViol++; } else if (r.R < T) nUnder++; }
      else { nB++; if (tB) thinBn++; }
    }
  }
  let lookFall = 0, lookFallMax = 0;
  const ls = (tr.looks || []).map(l => l.S);
  for (let a = 0; a < ls.length; a++) { let m = S; for (let b = a + 1; b < ls.length; b++) m = Math.min(m, ls[b]); if (ls[a] > m) { lookFall = 1; lookFallMax = Math.max(lookFallMax, ls[a] - m); } }
  const alFired = brd.alerts.filter(a => a.state === 'fired').length, alAband = brd.alerts.filter(a => a.state === 'abandoned' || a.state === 'pending').length;
  const lifted = brd.events.some(e => e.lift && e.after > e.before) ? 1 : 0;
  // N5 residue: Rivals whose residue mod 20 first appears on their last event; N6: the up-neighbour is a leader
  let resLast = 0, resDen = 0, settles = 0;
  for (const r of riv) {
    settles += r.settles;
    const ups = r.evs.filter(e => e.after > e.before && e.t >= tM);
    if (ups.length >= 2 && r.R % 20 !== 0) { resDen++; if (ups[ups.length - 2].after % 20 === 0) resLast++; }
  }
  const nbLead = upI >= 0 ? (riv[upI].leader ? 1 : 0) : -1;
  const flagCode = flag === 'up' ? 1 : flag === 'dn' ? 2 : 0;
  const gs = brd.guardStat, cs = brd.capStat, guardRivals = riv.filter(r => r.gsteps > 0).length;
  const lookTs = (tr.looks || []).map(l => l.t); const guardNear = brd.events.filter(e => e.guard && lookTs.some(lt => e.t >= lt && e.t - lt <= B0.minSpacing)).length; // guard steps within one spacing window after a lookahead tick (a deferred scheduled move pre-empted by the guard)
  return { guardNear, latePassVis, L: brd.L, guardSteps: gs.steps, guardRivals, guardFail: gs.fails, capClimbs: cs.climbs, capBites: cs.bites, capViol, minGapAbove, lastUpPhi: lastUpT >= 0 && tEnd > 0 ? lastUpT / tEnd : -1, stall, relEvNG, shown, wrong, wrongOrder: shown !== k ? 1 : 0, wrongDown, wrongUp, wrongS45, gapUp, gapDn, violUp, violDn, floorBreak, ties, cuMeas, cdMeas, flagCode, bunch, nbLead, leadChanges, latePass, passes, lastPassPhi, latePlCross,
    rankMark: brd.markInfo ? brd.markInfo.rank : 0, finalR, alFired, alAband, nAl: brd.alerts.length, nBig, nFol, cov, covDen: tEnd + 1, nOver, maxOver, nUnder, thinAn, nA, thinBn, nB, rmaxN, rmaxDen, resLast, resDen, settles,
    mvUpPre, mvDnPre, mvUpPost, mvDnPost, lookFall, lookFallMax, relN, relEv, relStepMed: med(relSteps), lifted };
}
const KLlb = KL.lb, KLub = KL.ub;

// ---------- independent audit (G5 a-z, run on every round). Works only from the recorded events / arrays.
function audit(cfg, par, brd, tr, fin, round) {
  const B = cfg.board, v = {}; const bad = (k) => { v[k] = (v[k] || 0) + 1; };
  const W5 = par.bank.w5.classic, riv = brd.riv, tM = brd.tMarkEff, looks = tr.looks || [], Tg = brd.Tg, mi0 = brd.markInfo;
  const byR = riv.map(() => []);
  for (const e of brd.events) byR[e.i].push(e);
  const lookAt = t => { let L = null; for (const l of looks) if (l.t <= t) L = l; else break; return L; };
  const t16 = tr.dropTicks.length >= B.lookFromDrop ? tr.dropTicks[B.lookFromDrop - 1] : Infinity;
  const tLastLook = looks.length ? looks[looks.length - 1].t : Infinity;
  for (const r of riv) {
    let prevT = -1e9, prevAfter = 0, prevNG = -1e9; const win = [];
    for (const e of byR[r.i]) {
      if (e.after < e.before || e.before < prevAfter) bad('a:monotone');
      if (!e.guard && e.t - prevNG < B.minSpacing) bad('b:spacing'); // guard events are exempt (they never move the spacing clock)
      if (e.after - e.before > B.sCap) bad('b:step');
      if (e.after > e.before) {
        win.push([e.t, e.after - e.before]);
        const st = e.after - e.before; // step grid: pre-mark multiples of 20; from the mark multiples of 5 and >= minStep (a final settle may be smaller)
        if (!e.post) { if (st % 20 !== 0) bad('q:premark-grid'); }
        else if (st % B.postGrid !== 0) bad('q:postmark-grid'); else if (st < B.minStep && !(r.settles > 0)) bad('q:step<20');
      }
      const s = win.filter(w => w[0] > e.t - B.windowTicks).reduce((a, w) => a + w[1], 0); if (s > W5 + 1e-6) bad('b:window');
      if (e.after > e.before) {
        if (!e.post) { // (c) pre-mark caps
          const lead = r.leader && (tr.Ht[e.t] === undefined || tr.Ht[e.t] < B.hGate);
          const cp = lead ? Math.floor(B.leaderL * e.P / 20) * 20 + B.leaderF : Math.floor(B.nonLeaderCap * e.P / 20) * 20;
          if (e.after > cp) bad('c:premark-cap');
        } else if (r.set === 'B') { // (d) live B-cap (until the finishing window), (i) T_i^B(S_lo*)
          if (e.bump && fin && mi0) { // N1 (i-B): after a closing-window bump of a B-Rival, S_final - R_after >= m_dn(S_final) (20 for the flagged close-down Rival; an S45-stuck Rival is a counted wrong place)
            const gap = fin.Sfinal - e.after, need = mi0.roles.B.close === r.i ? 20 : mDn(cfg, fin.Sfinal), stuck = r.frozenEver && e.after > Tg.val(r.i, fin.Sfinal);
            if (gap < need && !stuck) bad('i:B-bump-margin');
          }
          if (!e.lift && !e.bump) {
            const inWin = fin && e.t >= fin.tEnd;
            if (!inWin && e.after > Math.max(0, Math.floor((B.bCap * e.P - B.bOff) / 20) * 20)) bad('d:B-cap');
            if (e.after > Tg.val(r.i, brd.sloArr[Math.min(e.t, brd.sloArr.length - 1)])) bad('i:B>T(Slo)');
          }
        } else if (r.set === 'A') { // (i) A <= max(T(S_lo*), T(latest S_look)); (j) late events only at lookahead ticks or in the closing window
          const L = lookAt(e.t), Sb = Math.max(brd.sloArr[Math.min(e.t, brd.sloArr.length - 1)], L ? L.S : 0);
          if (e.bump) { if (e.after > Math.max(Tg.val(r.i, Sb), e.before) + 5 * B.rivals) bad('i:bump-too-far'); } else if (e.after > Tg.val(r.i, Sb)) bad('i:A>T(S)'); // N1: a tie bump is measured from max(T_i, before) + 45
          const slo = brd.sloArr[Math.min(e.t, brd.sloArr.length - 1)];
          if (!e.bump && !(L && L.final) && !(fin && e.t >= fin.tEnd) && e.after > Tg.val(r.i, slo) + Math.max(B.late.O.frac * slo, B.late.O.abs)) bad('gg:cap'); // S80: non-final levels <= T_i(S_lo*) + O(S_lo*)
        }
      }
      if (e.guard) { // (ee) guard events: A-Rivals only, only once a lookahead exists, before t_End, from below the guard level to at most G = c5(P + m_up(P)); the cap/(j) checks do not apply
        const Gm = KL.c5(e.P + mUp(cfg, e.P));
        if (r.set !== 'A' || !lookAt(e.t) || (fin && e.t >= fin.tEnd) || e.before >= Gm || e.after > Gm || e.after <= e.before) bad('ee:guard');
      } else if (e.post && r.set === 'A' && e.t >= t16 && e.t < tLastLook) { // (j)
        const L = lookAt(e.t);
        if (!L || prevNG >= L.t) bad('j:A-event-off-lookahead');
      }
      prevT = e.t; prevAfter = e.after; if (!e.guard) prevNG = e.t;
    }
  }
  // at most L Rivals (the leaders) above P at every pre-mark tick (non-leaders sit below 0.9 P and never come down)
  const lim = Math.min(brd.tClose, isFinite(tM) ? tM - 1 : brd.tClose);
  for (let t = 0; t <= lim; t++) { const P = brd.Pof(t); let n = 0; for (const a of brd.Rt) if (a[t] > P) n++; if (n > brd.L) { bad('c:>L-above'); break; } }
  // (e) stream reads: rival reads only at the mark (tick tM); board reads only at init and pre-mark; alert reads only at init
  const rv = brd.reads.rival; if (rv.length && Math.min(...rv) < tM) bad('e:rival-read-before-mark');
  const bd = brd.reads.board; for (const x of bd) if (x >= tM && x >= 0) { bad('e:board-read-after-mark'); break; }
  for (const x of brd.reads.alert) if (x >= 0) { bad('e:alert-read-after-init'); break; }
  // (f) nominal spawns, j_1 band
  for (const s of round.spawns) if (s[2] > 3) bad('f:tier>3');
  for (const m of round.merges) if (Math.abs(m.j) > cfg.physics.jitterBand + 1e-9) bad('f:jitter');
  // (k) / (cc) bonus iff (k <= 2 and r_m - k >= d_b), at most once, only if the round reached the check without overflow
  const mi = brd.markInfo, expect = mi && mi.bonus && round.bonusChecked ? 1 : 0;
  if ((round.bonus ? 1 : 0) !== expect) bad('k:bonus-condition');
  if (mi) { const rk = 1 + mi.Rm.filter(x => x > mi.Pm).length; if (rk !== mi.rank) bad('k:rank-recompute'); if (mi.bonus !== ((par.place <= B.bonus.kMax) && rk - par.place >= B.bonus.db)) bad('k:bonus-recompute'); }
  if (round.place >= 3 && round.bonus) bad('k:bonus-place>=3');
  // (n) no alert delivered at or after t_m
  for (const a of brd.alerts) if (a.state === 'fired' && a.t >= tM) bad('n:alert-after-mark');
  // (o,w) the fixed read block at the mark: 27 + 3 reads, nothing before them; then exactly one tau read per A-Rival
  if (mi) {
    if (!(mi.vStart === 0 && mi.vReads === 4 * B.rivals + 3)) bad('o:v-order'); // bb: v, w, z, e, s, h, y
    const nA = riv.filter(r => r.set === 'A').length;
    if (brd.reads.rival.slice(0, mi.vReads + nA).some(x => x !== mi.t)) bad('w:read-block-tick');
  }
  // (p) S_lo*(t) <= S_final at every tick (a true bound)
  for (let t = 0; t < brd.sloArr.length; t++) if (brd.sloArr[t] > fin.Sfinal) { bad('p:Slo>Sfinal'); break; }
  // (h) alerts truthful: recompute from the arrays
  for (const a of brd.alerts) if (a.state === 'fired') {
    const i = a.rival, t = a.t, P = brd.Pof(t), Rn = brd.Rt[i][t], tp = Math.max(0, t - B.alert.lookbackTicks), gp = brd.Pof(tp) - brd.Rt[i][tp];
    const gn = P - Rn;
    if (!(Rn < P)) bad('h:not-behind');
    if (gn > Math.max(B.alert.within * P, B.alert.withinFloor) + 1e-9) bad('h:gap>15%');
    if (!(gp > 0 && gn <= (1 - B.alert.closeFrac) * gp + 1e-9)) bad('h:not-closed-1/3');
  }
  // (y) NLS: the leaders are the L Rivals with the highest a (ties by index); A = the k-1 Rivals with the smallest y (ties by index)
  if (mi) {
    const ld = riv.filter(r => r.leader), non = riv.filter(r => !r.leader);
    if (ld.length !== brd.L) bad('y:leader-count');
    if (ld.length && non.length) { const lo = ld.reduce((m, r) => (m === null || r.a < m.a || (r.a === m.a && r.i > m.i)) ? r : m, null), hi = non.reduce((m, r) => (m === null || r.a > m.a || (r.a === m.a && r.i < m.i)) ? r : m, null); if (lo.a < hi.a || (lo.a === hi.a && lo.i > hi.i)) bad('y:leaders-not-top-L'); }
    const k = par.place; const wantA = riv.slice().sort((x, y) => x.y - y.y || x.i - y.i).slice(0, k - 1).map(r => r.i).sort((x, y) => x - y);
    if (JSON.stringify(wantA) !== JSON.stringify(mi.A.slice().sort((x, y) => x - y))) bad('y:A-by-y');
    if (mi.A.length !== k - 1) bad('y:A-size');
  }
  // (gg) overshoot_i = R_final - T_i(S_final) <= O(S_final) + 45 for every A-Rival (a construction invariant; fails only on a bug)
  if (Tg) { const Sf = fin.Sfinal; for (const r of riv) if (r.set === 'A' && r.R - Tg.val(r.i, Sf) > Math.max(B.late.O.frac * Sf, B.late.O.abs) + 45) bad('gg:overshoot'); }
  // (r,t,x) the target law at S_final: neighbour = min/max-law inversion of v_nb (independent recomputation), others >= neighbour +- 5, A chain distinct, non-close targets carry the margins
  if (mi && Tg) {
    const S = fin.Sfinal, c = brd.ctx, KLm = KL;
    for (const side of ['A', 'B']) {
      const ord = Tg.order[side], A = side === 'A', sp = mi.roles[side];
      if (!ord.length) continue;
      const gS = 5 * (A ? Math.ceil(S / 5 - 1e-9) : Math.floor(S / 5 + 1e-9));
      const ch = Tg.chain(side, gS);
      for (let q = 1; q < ch.length; q++) if (A ? ch[q] < ch[q - 1] + 5 : (ch[q] > ch[q - 1] - 5 && ch[q] > 0)) bad('t:chain-distinct');
      if (sp.nb >= 0) {
        const nbq = Tg.pos[sp.nb], nbRaw = A ? KLm.nbA(c, gS, sp.vnb, sp.nN) : KLm.nbB(c, gS, sp.vnb, sp.nN);
        const want = (sp.close >= 0 ? (A ? Math.max(nbRaw.val, ch[0] + 5) : Math.min(nbRaw.val, ch[0] - 5)) : nbRaw.val);
        if (ch[nbq] !== (A ? Math.max(0, want) : Math.max(0, want))) bad('x:neighbour-law');
        for (let q = nbq + 1; q < ch.length; q++) if (A ? ch[q] < ch[nbq] + 5 : ch[q] > ch[nbq] - 5 && ch[nbq] >= 5) bad('x:others-beyond-neighbour');
        if (A && ch[nbq] < gS + c.mUp(gS) - 1e-9) bad('r:A-neighbour-margin'); if (!A && ch[nbq] > gS - c.mDn(gS) + 1e-9) bad('r:B-neighbour-margin');
      }
    }
  }
  return v;
}

// public Rival records: exactly {handle, icon, score, drops, place} (place = the Rival's place on the final board, the player included; ties go to the lower index)
function records(brd, Sfinal) {
  return brd.riv.map(r => {
    let above = Sfinal > r.R ? 1 : 0;
    for (const o of brd.riv) if (o !== r && (o.R > r.R || (o.R === r.R && o.i < r.i))) above++;
    return { handle: r.handle, icon: r.icon, score: r.R, drops: r.drops, place: 1 + above };
  });
}
// the player's place as read off the public records (independent of evaluate(): board = payout check)
function boardPlace(brd, Sfinal) { return 1 + records(brd, Sfinal).filter(x => x.score >= Sfinal).length; }

// ---------- the live board view (MATH_SPEC_6 section 8): a PURE function of the visible state {P: player score, rivals: [{i, handle, R}]}. It reads no draw, role, target, flag or stream.
// The top 3, the player and the player's above/below neighbours (deduplicated: 4-6 rows) and the header "Place p of 10". Ties (equal scores) break by Rival index; the player wins ties. No reward styling, no "live"/"online" label.
const BOARD_LABELS = { header: 'Place {p} of {n}', you: 'You' };
function boardView(vis, nPlaces) {
  const n = nPlaces || (vis.rivals.length + 1);
  const ent = vis.rivals.map(r => ({ who: r.handle, score: r.R, idx: r.i, you: false }));
  ent.push({ who: BOARD_LABELS.you, score: vis.P, idx: -1, you: true });
  ent.sort((a, b) => b.score - a.score || (a.you ? -1 : b.you ? 1 : a.idx - b.idx));
  const me = ent.findIndex(e => e.you), keep = new Set([0, 1, 2, me]); if (me > 0) keep.add(me - 1); if (me < ent.length - 1) keep.add(me + 1);
  const rows = []; ent.forEach((e, q) => { if (keep.has(q)) rows.push({ handle: e.who, score: e.score, place: q + 1, you: e.you }); });
  return { header: BOARD_LABELS.header.replace('{p}', String(me + 1)).replace('{n}', String(n)), rows };
}

module.exports = { runBoard, evaluate, audit, records, boardPlace, boardView, BOARD_LABELS, HANDLE_RE, FRUITS, PARTS, f20, c20, f5, c5, mDn, mUp, getCtx };
