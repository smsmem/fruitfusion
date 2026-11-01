'use strict';
// rivals_8.js — math_8 Rival board (MATH_SPEC_8 on rivals_7.js): fill-paced Rivals (phi from the landed-fruit area), the mark = release 16 (or the earlier first closing release), opening scores 5-55 on per-Rival residue grids,
// tie parity (player ≡ 0 mod 20, Rivals never), fork lookahead at every release (closing releases lift every A-Rival clear of the player's remaining Splay; the block frame is the final board, nothing after it),
// late phase (phi >= 0.85, settled pile >= 0.70 or a closing release) with the S80 cap and guard, rescue trigger (replaces bonus play), m_up = max(1% S, 100).
// (history) rivals_7.js / rivals_4.js. A PURE function of (streams, rating, bot, the player event trace, the fork results). runBoard() re-derives the whole board from the trace.
const KL = require('./kernlib.js');
const FRUITS = ['Peach', 'Plum', 'Cherry', 'Berry', 'Melon', 'Mango', 'Kiwi', 'Lime', 'Lemon', 'Grape', 'Pear', 'Fig', 'Apple', 'Guava', 'Papaya', 'Lychee'];
const PARTS = ['Pit', 'Pip', 'Seed', 'Peel', 'Rind', 'Zest', 'Stem', 'Leaf', 'Juice', 'Drop', 'Pop', 'Bloom', 'Slice', 'Core', 'Twist'];
const HANDLE_RE = /^(Peach|Plum|Cherry|Berry|Melon|Mango|Kiwi|Lime|Lemon|Grape|Pear|Fig|Apple|Guava|Papaya|Lychee)(Pit|Pip|Seed|Peel|Rind|Zest|Stem|Leaf|Juice|Drop|Pop|Bloom|Slice|Core|Twist)_[1-9][0-9]$/;
const f5 = KL.f5, c5 = KL.c5;
const a5u = v => { let x = c5(v); if (x % 20 === 0) x += 5; return x; };   // a5 up: next value of 5Z \ 20Z at or above v
const a5d = v => { let x = f5(v); if (x % 20 === 0) x -= 5; return x; };   // a5 down
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
    const X = par.bank.ref.topout[par.bot]; if (!X) throw new Error('no bank reference for bot ' + par.bot);
    c = KL.makeCtx(X, par.kern.bots[par.bot], s => mUp(cfg, s), s => mDn(cfg, s), { thinCap: B.thinCap });
    CTX.set(key, c);
  }
  return c;
}
// the G(phi) lookup (MATH_SPEC_8 5.2): G at phi_j = 0, 0.02, ..., 0.98 (stored), G(1) = 1; floor index (a step function)
const Gof = (arr, phi) => phi >= 1 ? 1 : arr[Math.min(arr.length - 1, Math.floor(phi / 0.02 + 1e-9))];

// par: {cfg, bank, kern, bot, place (null ok before the mark), rating}
// S: {board, rival, alert} fresh Xo streams. tr: {Pt[], Ht[], TB[], Am[] (running max of the landed area share), dropTicks[], tMark|null, looks[{t,n,S,Splay,closing,h}]}. upto: last tick to process (non-final run).
// fin (final run): {Sfinal, tEnd (= t_B), lastDropT}
function runBoard(par, S, tr, upto, fin) {
  const cfg = par.cfg, B = cfg.board, k = par.place, CK = cfg.clock;
  const rd = { board: [], rival: [], alert: [] }, cur = { t: -1 };
  const sb = tap(S.board, 'board', rd, cur), sr = tap(S.rival, 'rival', rd, cur), sa = tap(S.alert, 'alert', rd, cur);
  const W5 = par.bank.w5.topout, gArr = par.bank.g.topout, aB = CK.aB;
  const rpace = par.rating; // kappa = 1 (U1)
  // ---------- init (tick -1): board stream = handles, a_i, first gaps, slack, then the opening permutation pi (8 reads), then u_L and l_1..l_9; alert stream = count, times, designated Rivals
  const riv = [], used = new Set();
  for (let i = 0; i < B.rivals; i++) {
    let h, f, p, nn;
    do { f = sb.int(FRUITS.length); p = sb.int(PARTS.length); nn = 10 + sb.int(90); h = FRUITS[f] + PARTS[p] + '_' + nn; } while (used.has(h));
    used.add(h);
    riv.push({ i, handle: h, icon: FRUITS[f].toLowerCase(), a: 0, open: 0, R: 0, nextEv: 0, lastEv: -1e9, evs: [], drops: 0, leader: false, set: null, tau: 0, v: 0, w: 0, z: 0, frozen: false, frozenAtMark: false, frozenEver: false, desig: -1, recent: [], settles: 0 });
  }
  for (const r of riv) r.a = Math.min(B.aClamp[1], Math.max(B.aClamp[0], Math.exp(B.aSigma * sb.gauss())));
  const gapDraw = (s) => B.gapBase + Math.round(B.gapMedian * Math.exp(B.gapSigma * s.gauss()));
  for (const r of riv) r.nextEv = gapDraw(sb);
  for (const r of riv) r.slack = B.slackMax * sb.float(); // tie-breaker (U3)
  { // S96 (rev 1, S3): opening scores o_i = V[pi_i], V = (5, 10, 15, 25, 30, 35, 45, 50, 55); Fisher-Yates over 9 values = 8 reads. Each Rival lives on o_i + 20Z
    const V = B.open.slice(); for (let q = V.length - 1; q >= 1; q--) { const j = sb.int(q + 1); const tmp = V[q]; V[q] = V[j]; V[j] = tmp; }
    riv.forEach((r, i) => { r.open = V[i]; r.R = V[i]; });
  }
  const f20i = (r, x) => r.open + 20 * Math.floor((x - r.open) / 20), c20i = (r, x) => r.open + 20 * Math.ceil((x - r.open) / 20);
  const byA = riv.slice().sort((x, y) => y.a - x.a || x.i - y.i); // highest a first
  // S76 (NLS): u_L then l_1..l_9 from `board`; L ~ W_L (the natural place-at-the-mark law); leaders = the L Rivals with the highest a (ties by index)
  const uL = sb.float(); for (const r of riv) r.ell = sb.float();
  const WL = B.start.WL, WLt = WL.reduce((a, b) => a + b, 0); let Lc = 0, accL = 0; { const xL = uL * WLt; for (; Lc < WL.length - 1; Lc++) { accL += WL[Lc]; if (xL < accL) break; } }
  const Ln = Lc; for (let j = 0; j < Ln; j++) byA[j].leader = true;
  const nonLeaders = riv.filter(r => !r.leader);
  // alerts (pre-mark only, S56): count, firing release counts delta_j = n_m * U(lo, hi) (MATH_SPEC_8 4.3), designated non-leaders
  const ua = sa.float(); const nAl = ua < B.alert.probs[0] ? 0 : ua < B.alert.probs[0] + B.alert.probs[1] ? 1 : 2;
  const alerts = [];
  const alTimes = []; for (let j = 0; j < nAl; j++) alTimes.push(cfg.rules.mark.n * (B.alert.lo + (B.alert.hi - B.alert.lo) * sa.float()));
  alTimes.sort((x, y) => x - y);
  const pool = nonLeaders.slice(); const perm = [];
  while (pool.length) perm.push(pool.splice(sa.int(pool.length), 1)[0]);
  for (let j = 0; j < Math.min(nAl, perm.length); j++) { alerts.push({ j, phi: alTimes[j], rival: perm[j].i, state: 'pending', t: null }); perm[j].desig = j; }
  // ---------- helpers
  const Pt = tr.Pt, Ht = tr.Ht, TBr = tr.TB, Am = tr.Am, dts = tr.dropTicks;
  const looks = tr.looks || [];
  let lkPtr = -1;
  const tMarkEff = tr.tMark !== null && tr.tMark !== undefined ? tr.tMark : (fin ? fin.tEnd : Infinity);
  const stop = fin ? fin.tEnd : upto;
  const tB = fin ? fin.tEnd : Infinity;
  let dptr = 0, sloStar = 0;
  const capStat = { climbs: 0, bites: 0 }, guardStat = { steps: 0, fails: 0 }, settleLog = [];
  const Pof = t => { if (fin && t >= fin.tEnd) return fin.Sfinal; const i = t < Pt.length ? t : Pt.length - 1; return i < 0 ? 0 : Pt[i]; };
  const phiOf = t => { if (fin && t >= fin.tEnd) return 1; const i = t < Am.length ? t : Am.length - 1; return i < 0 ? 0 : Math.min(CK.phiCap, Am[i] / aB); };
  const gOf = t => Gof(gArr, phiOf(t));
  const Rat = (r, t) => { let v = r.open; for (let e = r.evs.length - 1; e >= 0; e--) if (r.evs[e].t <= t) { v = r.evs[e].after; break; } return v; };
  const sloArr = new Int32Array(stop + 1);
  const events = [];
  let markDone = false, markInfo = null, ctx = null;
  const ctxOf = () => ctx || (ctx = getCtx(par));
  let Tg = null;
  // late-start release (MATH_SPEC_8 5.5): the first post-mark release with phi >= phiLook, a settled pile >= hLate, or a closing flag (a closing mark release counts)
  let lateT = Infinity, lateLook = null;
  for (const l of looks) { if (l.t > tMarkEff || (l.t === tMarkEff && l.closing)) { if (l.closing || l.h >= CK.hLate || phiOf(l.t) >= CK.phiLook) { lateT = l.t; lateLook = l; break; } } }
  const allowed = (r, v, post) => post ? (v % 20 !== 0) : ((v - r.open) % 20 === 0);

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
    let A = [];
    if (k !== null && k !== undefined) A = riv.slice().sort((x, y) => x.y - y.y || x.i - y.i).slice(0, k - 1);
    for (const r of riv) r.set = 'B';
    for (const r of A) r.set = 'A';
    for (const a of alerts) if (a.state === 'pending') { a.state = 'abandoned'; a.t = t; } // give-up at the mark (S56)
    const nPlaces = B.places;
    const close = e < B.closeRate;
    const sideUp = (k === 1) ? false : (k === nPlaces) ? true : sCoin < 0.5;
    const closeSide = close && k !== null && k !== undefined ? (sideUp ? 'up' : 'dn') : null;
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
    const phim = phiOf(t);
    const lo = Math.min(phim + B.tauLoOffset, B.tauHi);
    for (const r of riv) if (r.set === 'A') r.tau = lo + (B.tauHi - lo) * sr.float();
    for (const r of riv) if (r.set === 'B' && r.R > Math.max(0, f5((B.bCap - r.slack) * Pm - B.bOff))) { r.frozen = true; r.frozenAtMark = true; r.frozenEver = true; }
    // rescue trigger (MATH_SPEC_8 3.3): a win draw at 1st or 2nd that sits >= d_r places behind its drawn place at the mark: k <= kMax and r_m - k >= d_r. Deterministic, no stream.
    const rescue = (k !== null && k !== undefined && k <= cfg.rescue.kMax) && (rank - k >= cfg.rescue.dr);
    markInfo = { t, Pm, rank, Rm, A: A.map(r => r.i), frozen: riv.filter(r => r.frozenAtMark).map(r => r.i), phi: phim, rescue, vStart: idx0, vReads: idx1 - idx0, v: riv.map(r => r.v), w: riv.map(r => r.w), z: riv.map(r => r.z), y: riv.map(r => r.y), L: Ln, leaders: riv.filter(r => r.leader).map(r => r.i),
      flag: { close, side: closeSide, e, s: sCoin, h }, roles: { A: specA, B: specB }, nbLeaderA: specA.nb >= 0 ? (riv[specA.nb].leader ? 1 : 0) : -1, nAbove: riv.filter(r => r.R > Pm && !r.leader).length };
  };

  const windowRem = (r, t) => { let s = 0; for (const e of r.recent) if (e[0] > t - B.windowTicks) s += e[1]; return Math.max(0, f5(W5 - s)); };
  const clashes = (r, v) => riv.some(o => o !== r && o.R === v);
  // apply: move R toward target, capped by step and 5 s window, landing on the allowed grid at every step (MATH_SPEC_8 6.2). Pre-mark steps are multiples of 20 (the Rival's own residue); from the mark on, landing values are in 5Z \ 20Z, steps are >= minStep
  // (a settle may be smaller). hardCeil: the largest value a tie bump may reach. exempt: a settle step (closing release / block frame), not subject to sCap / the 5 s window.
  const apply = (r, t, target, post, settleOK, hardCeil) => {
    const gain = target - r.R; if (gain <= 0) return 0;
    const avail = Math.min(B.sCap - r.evStep, windowRem(r, t), gain);
    let land;
    if (!post) { land = r.R + 20 * Math.floor(avail / 20); }
    else {
      let step = f5(avail);
      if (avail < gain) { const d = 5 * ((Math.floor(t / 5) + 3 * r.i) % 4); if (step - d >= B.minStep) step -= d; } // cap-limited climb: shave a deterministic 0-15 so residues mod 20 appear during the climb (N5)
      land = r.R + step;
      if (land % 20 === 0) land -= 5;
    }
    if (land <= r.R) return 0;
    let step = land - r.R, settle = false;
    if (post && step < B.minStep) {
      if (settleOK && gain < B.minStep) { // a final settle completes the target with a step under the minimum
        let l2 = r.R + f5(gain); if (l2 % 20 === 0) l2 -= 5;
        if (l2 > r.R && l2 - r.R <= Math.min(B.sCap - r.evStep, windowRem(r, t))) { land = l2; step = land - r.R; settle = true; } else return 0;
      } else return 0;
    }
    // Rival-Rival tie: take the next allowed value upward if within the event's caps, else hold
    const cap = Math.min(r.R + Math.min(B.sCap - r.evStep, windowRem(r, t)), hardCeil === undefined ? Infinity : hardCeil);
    let guard = 0;
    while (clashes(r, land) && guard++ < 8) { land += post ? 5 : 20; if (post && land % 20 === 0) land += 5; if (land > cap) return 0; }
    step = land - r.R; if (step <= 0) return 0;
    if (settle) r.settles++;
    r.R = land; r.evStep += step; r.recent.push([t, step]);
    return step;
  };
  // a settle step (closing release / block frame): exempt from sCap and the 5 s window, lands on 5Z \ 20Z (A: up), avoids ties
  const settleTo = (r, t, v, kind) => {
    v = a5u(v); if (v <= r.R) return 0;
    let g = 0; while (clashes(r, v) && g++ < 20) v = a5u(v + 5);
    const step = v - r.R; r.R = v; settleLog.push({ t, i: r.i, step, kind });
    return step;
  };
  const Ocap = x => Math.max(B.late.O.frac * x, B.late.O.abs);
  const nextSched = (r, t, post, late) => (!post) ? t + gapDraw(sb) : (r.set === 'A' && late) ? Infinity : t + gapDraw(sr);

  const processEvent = (r, t) => {
    cur.t = t;
    const post = t >= tMarkEff;
    const lk = lkPtr >= 0 ? looks[lkPtr] : null;
    const Pn = Pof(t), phi = phiOf(t);
    const late = t >= lateT;
    const before = r.R; r.evStep = 0;
    let lift = false;
    r.nextEv = nextSched(r, t, post, late);
    const pace = f20i(r, rpace * r.a * gOf(t));
    const al = r.desig >= 0 ? alerts[r.desig] : null;
    const alActive = al && al.state === 'pending' && !post;
    let cap, target;
    if (!post) {
      if (r.leader) { // S76: a leader sits in [P + 20, 1.25 P + 100]: min(cap_hi, max(pace, floor_i)); cap_hi = f20'(1.25 P) + 100 while the jar height Ht(t) < hGate, else f20'(0.90 P)
        const Hh = Ht[t] === undefined ? 1 : Ht[t]; cap = Hh < B.hGate ? f20i(r, B.leaderL * Pn) + B.leaderF : f20i(r, B.nonLeaderCap * Pn);
        const fl = c20i(r, Pn + B.start.band.off + r.ell * (B.start.band.frac * Pn + B.start.band.abs));
        target = Math.min(cap, Math.max(pace, fl));
      } else { cap = f20i(r, (B.nonLeaderCap - r.slack) * Pn); target = Math.min(pace, cap); }
    } else {
      const g = gOf(t), Slo = sloStar, TF = S0 => Tg.val(r.i, S0);
      let Sproj = Math.max(Slo, Pn);
      if (g > 0 && phi >= markInfo.phi) Sproj = Math.max(Sproj, Pn / g);
      if (r.set === 'B') {
        const Bcap = Math.max(0, f5((B.bCap - r.slack) * Pn - B.bOff));
        if (r.R > Bcap) { cap = Bcap; r.frozen = true; r.frozenEver = true; target = r.R; }
        else {
          r.frozen = false;
          const tb = late ? TF(Slo) : Math.min(TF(Slo), f5(TF(Sproj) * g));
          cap = Bcap; target = Math.min(tb, cap);
        }
      } else if (late) { // A, late phase: move toward T_i(max(S_n, S_lo*)) (the fork's settled projection), never below the true bound; S80: a non-closing climb stops at T_i(S_lo*) + O(S_lo*)
        const tFull = TF(Math.max(lk ? lk.S : 0, Slo));
        const capLvl = f5(TF(Slo) + Ocap(Slo));
        if (tFull > r.R) { capStat.climbs++; if (tFull > capLvl) capStat.bites++; }
        target = Math.min(tFull, capLvl); cap = target;
        if (lk && lk.closing && r.R < target) r.nextEv = t + B.minSpacing; // the remainder after a closing release respects the caps in (t_n, t_B]
      } else if (phi >= r.tau) { target = Math.min(TF(Slo), f5(TF(Sproj) * g)); cap = target; }
      else { cap = f5(0.97 * Pn); target = Math.min(f5(TF(Sproj) * g), cap); if (r.R > cap) target = r.R; }
    }
    if (alActive) target = Math.min(target, Math.max(f20i(r, B.alert.preCap * Pn), r.R));
    apply(r, t, target, post, false, !post ? cap : target);
    // ----- alert delivery (truthfulness enforced here and audited independently)
    if (alActive && al.state === 'pending' && dptr >= al.phi) {
      const prev = r.desig > 0 ? alerts[r.desig - 1] : null;
      const spaced = !prev || prev.state !== 'fired' || t - prev.t >= B.alert.minGapTicks;
      if (spaced && Pn > 0) {
        const tp = Math.max(0, t - B.alert.lookbackTicks);
        const gapPrev = Pof(tp) - Rat(r, tp);
        const needGap = Math.min(Math.max(B.alert.within * Pn, B.alert.withinFloor), (1 - B.alert.closeFrac) * gapPrev);
        const Rneed = c20i(r, Pn - needGap);
        const capNow = Math.min(Math.max(cap, 0) + B.slackMax * 2 * Pn, Math.max(0, f20i(r, B.bCap * Pn - B.bOff)), f20i(r, B.nonLeaderCap * Pn)); // same test for every rung (pre-mark only)
        if (gapPrev > 0 && Rneed <= capNow && Rneed < Pn) {
          if (Rneed > r.R) apply(r, t, Rneed, false, false, capNow);
          const gapNow = Pn - r.R;
          if (r.R < Pn && gapNow <= Math.max(B.alert.within * Pn, B.alert.withinFloor) + 1e-9 && gapNow <= (1 - B.alert.closeFrac) * gapPrev + 1e-9) { al.state = 'fired'; al.t = t; al.gapPrev = gapPrev; al.gapNow = gapNow; al.P = Pn; al.R = r.R; }
        }
      }
    }
    r.lastEv = t;
    if (r.R !== before) r.drops++;
    events.push({ t, i: r.i, before, after: r.R, P: Pn, post, lift, set: r.set });
    r.evs.push({ t, before, after: r.R });
  };

  // closing release (MATH_SPEC_8 5.4 C2): every A-Rival gets an event on this tick: settle step up to F_n = a5u(Splay_n + m_up(Splay_n)) (the flagged close-up Rival: a5u(Splay_n + 20 + h (m_up - 20))), then the capped climb toward min(T_i(S_n), T_i(S_lo*) + O(S_lo*))
  const closingEvent = (r, t, lk) => {
    cur.t = t; const before = r.R; r.evStep = 0;
    const TF = S0 => Tg.val(r.i, S0), Slo = sloStar;
    const T1 = Math.min(TF(Math.max(lk.S, Slo)), f5(TF(Slo) + Ocap(Slo)));
    const mu = mUp(cfg, lk.Splay), gl = B.late.guardLead;
    const F = markInfo.roles.A.close === r.i ? a5u(lk.Splay + gl + markInfo.flag.h * (mu - gl)) : a5u(lk.Splay + mu);
    r.Fn = Math.max(r.Fn || 0, F);
    if (F > r.R) settleTo(r, t, F, 'closing');
    apply(r, t, Math.max(r.R, T1), true, true, Math.max(r.R, T1));
    r.nextEv = r.R < T1 ? t + B.minSpacing : Infinity;
    r.lastEv = t;
    if (r.R !== before) r.drops++;
    events.push({ t, i: r.i, before, after: r.R, P: Pof(t), post: true, lift: false, set: 'A', closing: true });
    r.evs.push({ t, before, after: r.R });
  };

  // S80 guard (from the late-start release until t_B): an A-Rival below G_i(t) steps up to it (spacing and the 5 s window respected, a step may be < 20). It never moves a B-Rival.
  const guardTry = (r, t) => {
    const Pn = Pof(t), mu = mUp(cfg, Pn), gl = B.late.guardLead;
    const G = (markInfo.roles.A.close === r.i) ? a5u(Pn + gl + markInfo.flag.h * (mu - gl)) : a5u(Pn + mu);
    if (r.R >= G) { r.gfail = false; return; }
    const before = r.R; r.evStep = 0;
    apply(r, t, G, true, true, G + 60);
    const failNow = r.R < G; if (failNow && !r.gfail) guardStat.fails++; r.gfail = failNow;
    if (r.R === before) return;
    r.gT = t; r.drops++; guardStat.steps++; r.gsteps = (r.gsteps || 0) + 1;
    events.push({ t, i: r.i, before, after: r.R, P: Pn, post: true, lift: false, set: 'A', guard: true });
    r.evs.push({ t, before, after: r.R });
  };

  // block frame (C4): one atomic snapshot at t_B: P = S_final, every A-Rival = T_i(S_final), every B-Rival = T_B(S_final), then the clash bump. No Rival event after t_B.
  const blockFrame = t => {
    cur.t = t; const Sf = fin.Sfinal, TF = (r, S0) => Tg.val(r.i, S0);
    for (const r of riv) {
      const before = r.R; let v;
      if (r.set === 'A') v = a5u(TF(r, Sf));
      else { v = a5d(TF(r, Sf)); if (r.R >= Sf) v = a5u(Sf + mUp(cfg, Sf)); } // S52: a frozen Rival that ends above the player is lifted to the m_up gap
      if (v > r.R) { let g = 0; while (clashes(r, v) && g++ < 20) v = r.set === 'A' || r.R >= Sf ? a5u(v + 5) : a5d(v - 5); if (v > r.R) { settleLog.push({ t, i: r.i, step: v - r.R, kind: 'block' }); r.R = v; } }
      if (r.R !== before) { r.drops++; r.evs.push({ t, before, after: r.R }); events.push({ t, i: r.i, before, after: r.R, P: Sf, post: true, lift: false, set: r.set, block: true }); }
    }
    // final clash bump: A up by 5, B down by 5 (skipping 20Z); a B bump never crosses m_dn; if impossible the B-Rival bumps up instead
    for (const r of riv) {
      let g = 0;
      while ((riv.some(o => o !== r && o.R === r.R) || r.R === Sf || r.R % 20 === 0) && g++ < 20) {
        const before = r.R; let v;
        if (r.R > Sf) v = a5u(r.R + (r.R % 20 === 0 ? 0 : 5));
        else { v = a5d(r.R - (r.R % 20 === 0 ? 0 : 5)); if (v < 0 || v > Sf - mDn(cfg, Sf) + 1e-9) v = a5u(r.R + 5); }
        if (v === r.R) v = a5u(r.R + 5);
        r.R = v; r.evs.push({ t, before, after: r.R }); events.push({ t, i: r.i, before, after: r.R, P: Sf, post: true, lift: false, set: r.set, block: true, bump: true });
      }
    }
  };
  // ---------- main loop
  for (let t = 0; t <= stop; t++) {
    cur.t = t;
    while (dptr < dts.length && dts[dptr] <= t) dptr++;
    let sl;
    if (fin && t >= fin.tEnd) sl = fin.Sfinal; else if (t < Pt.length) sl = Pt[t] + Math.floor(B.sloFrac * Math.max(0, (TBr ? (TBr[t] || 0) : 0) - 40)); else sl = 0;
    if (sl > sloStar) sloStar = sl;
    sloArr[t] = sloStar;
    const arrivedNow = [];
    while (lkPtr + 1 < looks.length && looks[lkPtr + 1].t <= t) { lkPtr++; arrivedNow.push(looks[lkPtr]); }
    if (!markDone && t >= tMarkEff) doMark(t);
    if (fin && t >= tB) { if (markDone) blockFrame(t); continue; }
    if (markDone) for (const lk of arrivedNow) for (const r of riv) if (r.set === 'A') { if (lk.closing) closingEvent(r, t, lk); else if (t >= lateT) r.nextEv = Math.max(t, r.lastEv + B.minSpacing); }
    for (const r of riv) if (r.nextEv === t && r.lastEv !== t) processEvent(r, t);
    if (markDone && t >= lateT) for (const r of riv) if (r.set === 'A' && r.gT !== t) guardTry(r, t);
  }
  if (!markDone && fin) { doMark(Math.min(stop, tMarkEff === Infinity ? stop : tMarkEff)); }
  // ---------- outputs
  const len = stop + 1;
  const Rt = riv.map(r => { const a = new Int32Array(len); let v = r.open, e = 0; for (let t = 0; t < len; t++) { while (e < r.evs.length && r.evs[e].t <= t) { v = r.evs[e].after; e++; } a[t] = v; } return a; });
  return { riv, alerts, events, Rt, markInfo, tMarkEff, tClose: stop, reads: rd, Pof, phiOf, looks, sloArr, Tg, ctx, L: Ln, capStat, guardStat, settleLog, lateT: isFinite(lateT) ? lateT : null, lateLook, par: { place: k } };
}

const med = a => { if (!a.length) return -1; const s = a.slice().sort((x, y) => x - y); return s[Math.floor(s.length / 2)]; };
const KLlb = KL.lb, KLub = KL.ub;
// ---------- evaluation of a finished round (fin given): shown place (= paid place), margins (neighbours only), wrong places, ties on every snapshot, passes by phase, settle / pomegranate quantities
function evaluate(cfg, brd, tr, fin, k, round) {
  const B0 = cfg.board, CK = cfg.clock;
  const riv = brd.riv, S = fin.Sfinal, finalR = riv.map(r => r.R);
  const shown = 1 + finalR.filter(v => v >= S).length;
  const wrongDown = shown > k ? 1 : 0, wrongUp = shown < k ? 1 : 0;
  const mu = mUp(cfg, S), md = mDn(cfg, S);
  let upI = -1, dnI = -1;
  for (const r of riv) { if (r.R >= S) { if (upI < 0 || r.R < riv[upI].R) upI = r.i; } else if (dnI < 0 || r.R > riv[dnI].R) dnI = r.i; }
  const gapUp = upI >= 0 ? riv[upI].R - S : null, gapDn = dnI >= 0 ? S - riv[dnI].R : null;
  const stuck = r => r.set === 'B' && r.frozenEver && brd.Tg && r.R > brd.Tg.val(r.i, S);
  let wrongS45 = 0; for (const r of riv) if (r.R < S && S - r.R < md && stuck(r)) wrongS45 = 1;
  const flag = brd.markInfo && brd.markInfo.flag ? brd.markInfo.flag.side : null;
  const cuMeas = gapUp !== null && gapUp < mu ? 1 : 0, cdMeas = gapDn !== null && gapDn < md ? 1 : 0;
  const violUp = cuMeas && flag !== 'up' ? 1 : 0;
  const violDn = cdMeas && flag !== 'dn' && !stuck(riv[dnI]) ? 1 : 0;
  const floorBreak = ((gapUp !== null && gapUp < 20) || (gapDn !== null && gapDn < 20)) ? 1 : 0;
  let ties = 0; { const all = finalR.concat([S]).sort((x, y) => x - y); for (let i = 1; i < all.length; i++) if (all[i] === all[i - 1]) ties++; }
  const wrong = wrongDown || wrongUp || wrongS45 ? 1 : 0;
  const above = finalR.filter(v => v >= S); let bunch = -1;
  if (above.length >= 2) bunch = (Math.max(...above) - Math.min(...above)) <= Math.max(0.02 * S, 40) ? 1 : 0;
  // per tick over the round (the player is index -1 and wins nothing: ties are counted): lead changes, place moves, snapshot ties (start, every tick, final), parity, passes by phase
  const tEnd = fin.tEnd, Pof = brd.Pof, Rt = brd.Rt;
  const tM = brd.markInfo ? brd.markInfo.t : tEnd;
  const dts = tr.dropTicks, tLast = dts.length ? dts[dts.length - 1] : 0;
  const lateT = brd.lateT === null ? Infinity : brd.lateT;
  const lastInp = round.inputs.length ? round.inputs[round.inputs.length - 1].t : -1;
  let leader = -1, leadChanges = 0, prevPl = 1, mvUpPre = 0, mvDnPre = 0, mvUpPost = 0, mvDnPost = 0, lastUpT = -1;
  let tieSnaps = 0, tieRP = 0, parityBad = 0, passLate = 0, passAfterLast = 0, passAtLast = 0, passWalk = 0, passAny = 0, minGapLate = -1;
  const passRivals = new Set();
  const vals = new Array(riv.length);
  for (let t = 0; t <= tEnd; t++) {
    const P = Pof(t); let best = -1, bv = P, pl = 1;
    for (let i = 0; i < Rt.length; i++) { const v = Rt[i][t]; vals[i] = v; if (v > bv) { bv = v; best = i; } if (v > P) pl++; if (v === P) tieRP++; }
    if (t < tEnd && P % 20 !== 0) parityBad++;
    for (let i = 0; i < vals.length; i++) { const v = vals[i]; if (v % 20 === 0 && !(t >= tEnd && false)) parityBad++; for (let j = i + 1; j < vals.length; j++) if (vals[j] === v) tieSnaps++; }
    if (t > 0 && best !== leader) leadChanges++;
    leader = best;
    if (t > 0 && pl !== prevPl) { if (pl < prevPl) { if (t < tM) mvUpPre++; else { mvUpPost++; lastUpT = t; } } else { if (t < tM) mvDnPre++; else mvDnPost++; } }
    prevPl = pl;
    if (t > 0) for (let i = 0; i < Rt.length; i++) if (Rt[i][t - 1] <= Pof(t - 1) && Rt[i][t] > P) { // visible form: behind or level at t-1, ahead at t
      passAny++; passRivals.add(i);
      if (t > lateT) passLate++;
      if (t > tLast) passAfterLast++; else if (t === tLast) passAtLast++;
      if (t > lastInp && t <= tLast) passWalk++;
    }
    if (t >= lateT && t < tEnd) for (let i = 0; i < Rt.length; i++) { const v = Rt[i][t]; if (v > P && (minGapLate < 0 || v - P < minGapLate)) minGapLate = v - P; }
  }
  tieSnaps += tieRP;
  const eventsAfterTB = brd.events.filter(e => e.t > tEnd).length;
  // visible-form late pass at the same tick form (reported): event based
  let latePassEv = 0; for (const e of brd.events) if (e.after > e.before && e.before <= Pof(e.t) && e.after > Pof(e.t) && e.t > lateT && !e.block) latePassEv++;
  // A-Rivals still behind the player at the last release tick (not yet lifted)
  let behindAtLast = 0; if (dts.length) for (const r of riv) if (r.set === 'A' && Rt[r.i][tLast] <= Pof(tLast)) behindAtLast++;
  // guard / steps
  const gs = brd.guardStat, cs = brd.capStat, guardRivals = riv.filter(r => r.gsteps > 0).length;
  const stepsLate = []; for (const e of brd.events) if (e.after > e.before && !e.block && e.t > lateT) stepsLate.push(e.after - e.before);
  let max1 = 0, max5s = 0; { for (const r of riv) { const evs = r.evs; for (let a = 0; a < evs.length; a++) { max1 = Math.max(max1, evs[a].after - evs[a].before); let s = 0; for (let b = a; b < evs.length && evs[b].t < evs[a].t + 300; b++) s += evs[b].after - evs[b].before; max5s = Math.max(max5s, s); } } }
  const setC = brd.settleLog.filter(s => s.kind === 'closing'), setB = brd.settleLog.filter(s => s.kind === 'block');
  // overshoot / undershoot of the A-Rivals against T_i(S_final)
  const Ocap = x => Math.max(B0.late.O.frac * x, B0.late.O.abs); let capViol = 0;
  let nOver = 0, maxOver = 0, nUnder = 0, thinAn = 0, nA = 0, thinBn = 0, nB = 0, rmaxN = 0, rmaxDen = 0, ovGt01 = 0, ovGt025 = 0, ovGtO = 0;
  if (brd.ctx && brd.Tg) {
    const c = brd.ctx, Tg = brd.Tg;
    const tA = c.N - KLlb(c.X, S + c.mUp(S)) <= 0, tB = KLub(c.X, S - c.mDn(S)) <= 0;
    for (const r of riv) {
      if (Tg.side[r.i] === undefined) continue;
      rmaxDen++; if (Tg.val(r.i, S) > Tg.raw(r.i, S)) rmaxN++;
      if (r.set === 'A') { nA++; if (tA) thinAn++; const T = Tg.val(r.i, S); if (r.R > T) { nOver++; const ov = r.R - T; maxOver = Math.max(maxOver, ov); if (ov > 0.1 * S) ovGt01++; if (ov > 0.25 * S) ovGt025++; if (ov > Ocap(S)) ovGtO++; if (ov > Ocap(S) + Math.max(45, mu + 5)) capViol++; } else if (r.R < T) nUnder++; }
      else { nB++; if (tB) thinBn++; }
    }
  }
  const alFired = brd.alerts.filter(a => a.state === 'fired').length, alAband = brd.alerts.filter(a => a.state === 'abandoned' || a.state === 'pending').length;
  const lifted = brd.events.some(e => e.lift && e.after > e.before) ? 1 : 0;
  let resLast = 0, resDen = 0, settles = 0;
  for (const r of riv) {
    settles += r.settles;
    const ups = r.evs.filter(e => e.after > e.before && e.t >= tM);
    if (ups.length >= 2 && r.R % 20 !== 0) { resDen++; if (ups[ups.length - 2].after % 20 === 0) resLast++; }
  }
  const nbLead = upI >= 0 ? (riv[upI].leader ? 1 : 0) : -1;
  const flagCode = flag === 'up' ? 1 : flag === 'dn' ? 2 : 0;
  // late start: round share by release count, releases left; rev-0 rule (h_late 0.80) on the same round
  const nRel = dts.length; let lateN = -1; if (brd.lateLook) lateN = brd.lateLook.n;
  let lateN80 = -1; for (const l of tr.looks) if (l.t > brd.tMarkEff || (l.t === brd.tMarkEff && l.closing)) { if (l.closing || l.h >= 0.80 || brd.phiOf(l.t) >= CK.phiLook) { lateN80 = l.n; break; } }
  const closings = tr.looks.filter(l => l.closing).length;
  const mi = brd.markInfo, rs = round.rescue;
  const pomReg = round.pomReleased.filter(p => p.regular && !p.pull).length, pomPull = round.pomReleased.filter(p => p.pull).length;
  const nonLeaderAbove = mi ? mi.nAbove : 0;
  return { tieSnaps, tieRP, parityBad, passLate, passAfterLast, passAtLast, passWalk, passAny, passRivals: passRivals.size, eventsAfterTB, latePassEv, behindAtLast, minGapLate, lateN, lateN80, nRel, closings, lateTick: brd.lateT === null ? -1 : brd.lateT,
    guardSteps: gs.steps, guardRivals, guardFail: gs.fails, capClimbs: cs.climbs, capBites: cs.bites, capViol, max1, max5s, setCn: setC.length, setCmax: setC.length ? Math.max(...setC.map(s => s.step)) : 0, setBn: setB.length, setBmax: setB.length ? Math.max(...setB.map(s => s.step)) : 0,
    stepLateMed: med(stepsLate), shown, wrong, wrongOrder: shown !== k ? 1 : 0, wrongDown, wrongUp, wrongS45, gapUp, gapDn, violUp, violDn, floorBreak, ties, cuMeas, cdMeas, flagCode, bunch, nbLead, leadChanges, minGapAbove: minGapLate, lastUpPhi: lastUpT >= 0 && tEnd > 0 ? lastUpT / tEnd : -1,
    rankMark: mi ? mi.rank : 0, finalR, alFired, alAband, nAl: brd.alerts.length, nOver, maxOver, nUnder, thinAn, nA, thinBn, nB, rmaxN, rmaxDen, ovGt01, ovGt025, ovGtO, resLast, resDen, settles, mvUpPre, mvDnPre, mvUpPost, mvDnPost, lifted, L: brd.L,
    pomReg, pomPull, pomAll: round.pomReleased.length, pops: round.pomPops, rescueFlag: rs.flag ? 1 : 0, rescueStarted: rs.started ? 1 : 0, rescuePulls: rs.pulls, rescuePlanned: rs.planned.length, markEarly: rs.markEarly ? 1 : 0, nonLeaderAbove,
    stall: -1 };
}

// ---------- independent audit (G5, run on every round). Works only from the recorded events / arrays.
function audit(cfg, par, brd, tr, fin, round, ev) {
  const B = cfg.board, v = {}; const bad = (k) => { v[k] = (v[k] || 0) + 1; };
  const W5 = par.bank.w5.topout, riv = brd.riv, tM = brd.tMarkEff, looks = tr.looks || [], Tg = brd.Tg, mi0 = brd.markInfo;
  const byR = riv.map(() => []);
  for (const e of brd.events) byR[e.i].push(e);
  const settleAt = new Map(); for (const s of brd.settleLog) settleAt.set(s.t + ':' + s.i + ':' + s.kind, s.step);
  const lookAt = t => { let L = null; for (const l of looks) if (l.t <= t) L = l; else break; return L; };
  const lateT = brd.lateT === null ? Infinity : brd.lateT, tB = fin.tEnd;
  const closingT = new Set(looks.filter(l => l.closing).map(l => l.t));
  const tLast = tr.dropTicks[tr.dropTicks.length - 1];
  for (const r of riv) {
    let prevAfter = r.open, prevNG = -1e9; const win = [];
    for (const e of byR[r.i]) {
      if (e.t > tB) bad('hh:event-after-tB');
      if (e.after < e.before || e.before < prevAfter) bad('a:monotone');
      const exempt = e.block ? 0 : (settleAt.get(e.t + ':' + e.i + ':closing') || 0);
      const regular = e.after - e.before - exempt;
      if (!e.guard && !e.block && !e.closing && e.t - prevNG < B.minSpacing) bad('b:spacing');
      if (!e.block && regular > B.sCap) bad('b:step');
      if (e.after > e.before) {
        if (!e.block && regular > 0) win.push([e.t, regular]);
        // (ii) parity: pre-mark e.after ≡ open (mod 20); from the mark on e.after ≢ 0 (mod 20) (the block frame included)
        if (!e.post) { if ((e.after - r.open) % 20 !== 0) bad('ii:premark-residue'); } else if (e.after % 20 === 0) bad('ii:postmark-mod20');
        const st = e.after - e.before; // step grid
        if (!e.post) { if (st % 20 !== 0) bad('q:premark-grid'); }
        else if (st % B.postGrid !== 0) bad('q:postmark-grid'); else if (st < B.minStep && !(r.settles > 0) && !exempt && !e.block && !e.guard) bad('q:step<20');
        if (!e.post && !e.block) { // (c1) pre-mark caps on the Rival's own grid
          const f20i = x => r.open + 20 * Math.floor((x - r.open) / 20);
          const lead = r.leader && (tr.Ht[e.t] === undefined || tr.Ht[e.t] < B.hGate);
          const cp = lead ? f20i(B.leaderL * e.P) + B.leaderF : f20i(B.nonLeaderCap * e.P);
          if (e.after > cp) bad('c:premark-cap');
        } else if (r.set === 'B' && !e.block) {
          if (!e.lift) {
            if (e.after > Math.max(0, Math.floor((B.bCap * e.P - B.bOff) / 20) * 20) + 20) bad('d:B-cap');
            if (e.after > Tg.val(r.i, brd.sloArr[Math.min(e.t, brd.sloArr.length - 1)])) bad('i:B>T(Slo)');
          }
        } else if (r.set === 'A' && !e.block && !e.guard) {
          const L = lookAt(e.t), slo = brd.sloArr[Math.min(e.t, brd.sloArr.length - 1)], Sb = Math.max(slo, L ? L.S : 0);
          if (e.after > Math.max(Tg.val(r.i, Sb), (e.closing ? (r.Fn || 0) : 0)) + 5) bad('i:A>T(S)');
          if (!e.closing && e.after > Tg.val(r.i, slo) + Math.max(B.late.O.frac * slo, B.late.O.abs) + 5) bad('gg:cap');
        }
      }
      const s = win.filter(w => w[0] > e.t - B.windowTicks).reduce((a, w) => a + w[1], 0); if (s > W5 + 1e-6) bad('b:window');
      if (e.guard) {
        const Gm = a5u(e.P + mUp(cfg, e.P));
        if (r.set !== 'A' || e.t < lateT || e.t >= tB || e.before >= Gm || e.after > Gm + 60 || e.after <= e.before) bad('ee:guard');
        if (e.t > tLast) bad('pp:guard-after-last');
      }
      if (e.post && r.set === 'A' && !e.guard && !e.block && !e.closing && e.t >= lateT && !(lookAt(e.t) && (lookAt(e.t).t === e.t || prevNG >= lookAt(e.t).t || true))) bad('j:A-event-off-lookahead');
      if (e.closing && !closingT.has(e.t)) bad('qq:settle-off-closing');
      if (!e.guard) prevNG = e.t;
      prevAfter = e.after;
    }
  }
  for (const s of brd.settleLog) if (s.kind === 'closing' ? !closingT.has(s.t) : s.t !== tB) bad('qq:settle-not-closing-or-block');
  // (c2) at most L Rivals above P at every pre-mark tick with P >= 60
  const lim = Math.min(brd.tClose, isFinite(tM) ? tM - 1 : brd.tClose);
  for (let t = 0; t <= lim; t++) { const P = brd.Pof(t); if (P < 60) continue; let n = 0; for (const a of brd.Rt) if (a[t] > P) n++; if (n > brd.L) { bad('c:>L-above'); break; } }
  // (e) stream reads
  const rv = brd.reads.rival; if (rv.length && Math.min(...rv) < tM) bad('e:rival-read-before-mark');
  const bd = brd.reads.board; for (const x of bd) if (x >= tM && x >= 0) { bad('e:board-read-after-mark'); break; }
  for (const x of brd.reads.alert) if (x >= 0) { bad('e:alert-read-after-init'); break; }
  // (f) spawns tiers 0-3 or the pomegranate (10); j_1 band
  for (const s of round.spawns) if (s[2] > 3 && s[2] !== 10) bad('f:tier');
  for (const m of round.merges) if (Math.abs(m.j) > cfg.physics.jitterBand + 1e-9) bad('f:jitter');
  // (nn) rescue iff k <= kMax and r_m - k >= d_r; post-mark only; <= 1 episode and <= 2 pull-ins
  const mi = brd.markInfo;
  if (mi) { const rk = 1 + mi.Rm.filter(x => x > mi.Pm).length; if (rk !== mi.rank) bad('nn:rank-recompute'); if (mi.rescue !== ((par.place <= cfg.rescue.kMax) && rk - par.place >= cfg.rescue.dr)) bad('nn:rescue-recompute'); }
  if (round.rescue.flag !== !!(mi && mi.rescue) && !round.o.noRescue) bad('nn:flag-vs-board');
  if (round.place >= 3 && (round.rescue.flag || round.rescue.started)) bad('nn:rescue-place>=3');
  if (round.rescue.started && (round.rescue.nr <= round.markN)) bad('nn:rescue-before-mark');
  if (round.rescue.q.length > cfg.rescue.pulls) bad('nn:pulls>cap');
  // (mm) pomegranate rules: pops <= popCap, tier <= popTierMax, gaps in [gapLo, gapHi], one spawn read per slot, score 0
  for (const p of round.pomLog) { if (p.pops.length > cfg.pom.popCap) bad('mm:pops>cap'); for (const q of p.pops) if (q[1] > cfg.pom.popTierMax) bad('mm:pop-tier'); }
  { const ps = round.pomReleased.map(p => p.n); for (let q = 1; q < ps.length; q++) { const g = ps[q] - ps[q - 1]; if (g < cfg.pom.gapLo || g > cfg.pom.gapHi) bad('mm:gap'); } if (ps.length && ps[0] < cfg.pom.gapLo) bad('mm:first-gap'); }
  if (round.spawns.length < round.drops + 1) bad('mm:spawn-count');
  // (n) no alert delivered at or after t_m
  for (const a of brd.alerts) if (a.state === 'fired' && a.t >= tM) bad('n:alert-after-mark');
  // (o,w) the fixed read block at the mark: 27 + 3 + 9 reads, nothing before them; then exactly one tau read per A-Rival
  if (mi) {
    if (!(mi.vStart === 0 && mi.vReads === 4 * B.rivals + 3)) bad('o:v-order');
    const nA = riv.filter(r => r.set === 'A').length;
    if (brd.reads.rival.slice(0, mi.vReads + nA).some(x => x !== mi.t)) bad('w:read-block-tick');
  }
  // (ll) S_lo*(t) <= S_final at every tick
  for (let t = 0; t < brd.sloArr.length; t++) if (brd.sloArr[t] > fin.Sfinal) { bad('ll:Slo>Sfinal'); break; }
  // (h) alerts truthful
  for (const a of brd.alerts) if (a.state === 'fired') {
    const i = a.rival, t = a.t, P = brd.Pof(t), Rn = brd.Rt[i][t], tp = Math.max(0, t - B.alert.lookbackTicks), gp = brd.Pof(tp) - brd.Rt[i][tp];
    const gn = P - Rn;
    if (!(Rn < P)) bad('h:not-behind');
    if (gn > Math.max(B.alert.within * P, B.alert.withinFloor) + 1e-9) bad('h:gap>15%');
    if (!(gp > 0 && gn <= (1 - B.alert.closeFrac) * gp + 1e-9)) bad('h:not-closed-1/3');
  }
  // (y) NLS: leaders = top-L a; A = the k-1 Rivals with the smallest y
  if (mi) {
    const ld = riv.filter(r => r.leader), non = riv.filter(r => !r.leader);
    if (ld.length !== brd.L) bad('y:leader-count');
    if (ld.length && non.length) { const lo = ld.reduce((m, r) => (m === null || r.a < m.a || (r.a === m.a && r.i > m.i)) ? r : m, null), hi = non.reduce((m, r) => (m === null || r.a > m.a || (r.a === m.a && r.i < m.i)) ? r : m, null); if (lo.a < hi.a || (lo.a === hi.a && lo.i > hi.i)) bad('y:leaders-not-top-L'); }
    const k = par.place; const wantA = riv.slice().sort((x, y) => x.y - y.y || x.i - y.i).slice(0, k - 1).map(r => r.i).sort((x, y) => x - y);
    if (JSON.stringify(wantA) !== JSON.stringify(mi.A.slice().sort((x, y) => x - y))) bad('y:A-by-y');
    if (mi.A.length !== k - 1) bad('y:A-size');
  }
  // opening scores: distinct, from V, not multiples of 20
  { const op = riv.map(r => r.open); if (new Set(op).size !== op.length || op.some(x => !B.open.includes(x) || x % 20 === 0)) bad('g4:opening'); }
  // (gg) overshoot
  if (Tg) { const Sf = fin.Sfinal; for (const r of riv) if (r.set === 'A' && r.R - Tg.val(r.i, Sf) > Math.max(B.late.O.frac * Sf, B.late.O.abs) + Math.max(45, mUp(cfg, Sf) + 5)) bad('gg:overshoot'); }
  // (hh)(jj)(kk)(oo)(pp): ties, passes after the last release, last release closing, the mark, A >= F_n after each closing release
  if (ev) { if (ev.tieSnaps > 0) bad('hh:tie-snapshot'); if (ev.parityBad > 0) bad('ii:parity-snapshot'); if (ev.passAfterLast > 0) bad('jj:pass-after-last'); if (ev.eventsAfterTB > 0) bad('jj:event-after-tB'); }
  { const last = looks[looks.length - 1]; if (!last || !last.closing) bad('kk:last-release-not-closing'); }
  if (mi) { const firstClosing = looks.find(l => l.closing); const expect = round.drops >= cfg.rules.mark.n && !(firstClosing && firstClosing.n < cfg.rules.mark.n) ? tr.dropTicks[cfg.rules.mark.n - 1] : firstClosing ? firstClosing.t : null; if (expect !== mi.t) bad('oo:mark'); }
  for (const l of looks) if (l.closing && l.t >= tM) for (const r of riv) if (r.set === 'A') {
    const F = (mi && mi.roles.A.close === r.i) ? a5u(l.Splay + B.late.guardLead + mi.flag.h * (mUp(cfg, l.Splay) - B.late.guardLead)) : a5u(l.Splay + mUp(cfg, l.Splay));
    const Pmax = l.Splay; // P(t) <= Splay_n until the next release
    let t2 = l.t; const nextRel = tr.dropTicks.find(d => d > l.t); const endT = nextRel === undefined ? tB : Math.min(nextRel, tB);
    if (brd.Rt[r.i][Math.min(endT - 1, brd.Rt[r.i].length - 1)] < F && endT - 1 >= l.t) { bad('pp:A<Fn'); break; }
    for (let t = l.t; t < endT && t < brd.Rt[r.i].length; t++) { if (brd.Rt[r.i][t] <= brd.Pof(t) && t < tB) { bad('jj:crossed-in-closing-interval'); break; } }
  }
  // (r,t,x) the target law at S_final
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

// public Rival records: exactly {handle, icon, score, drops, place}
function records(brd, Sfinal) {
  return brd.riv.map(r => {
    let above = Sfinal > r.R ? 1 : 0;
    for (const o of brd.riv) if (o !== r && (o.R > r.R || (o.R === r.R && o.i < r.i))) above++;
    return { handle: r.handle, icon: r.icon, score: r.R, drops: r.drops, place: 1 + above };
  });
}
function boardPlace(brd, Sfinal) { return 1 + records(brd, Sfinal).filter(x => x.score >= Sfinal).length; }

// ---------- the live board view (MATH_SPEC_6 section 8): a PURE function of the visible state {P, rivals: [{i, handle, R}]}.
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

module.exports = { runBoard, evaluate, audit, records, boardPlace, boardView, BOARD_LABELS, HANDLE_RE, FRUITS, PARTS, f5, c5, a5u, a5d, mDn, mUp, getCtx, Gof };
