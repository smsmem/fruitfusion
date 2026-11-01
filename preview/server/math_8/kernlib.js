'use strict';
// kernlib.js — math_7 Rival target construction (MATH_SPEC_6 section 2, family 3): honest-law neighbour + capped-kernel others, on a 5-point grid.
// Shared by rivals_7.js (live), tools/kern7.js (offline fit), tools/natural7.js and report_7.js. Pure, no I/O.
// Per side (A = Rivals that finish above the player, B = below):
//   close Rival  : T_c(S) = ceil5(S + 20 + h (m_up(S) - 20))  /  floor5(S - 20 - h (m_dn(S) - 20))
//   neighbour    : the atom at the min (A) / max (B) law inversion of v_nb over A(S) / B(S) (the lowest of n iid honest draws), no jitter
//   others       : position beyond the neighbour from the per-bot, per-player-quantile kernel kappa[u][l] at the stratified v', atom, w-jitter to the next atom, 5-grid, >= neighbour +- 5
//   chain        : taken in ascending v' order after the neighbour: T_(j) = max(raw_(j), T_(j-1) + 5) (B mirrored with -5)
//   running max  : T_i(S) = max over the 5-point grid up to ceil5(S) (A) / floor5(S) (B) of the chain target, so a recomputed target never asks a Rival to go down.
const f5 = v => Math.floor(v / 5 + 1e-9) * 5;
const c5 = v => Math.ceil(v / 5 - 1e-9) * 5;
function lb(A, x) { let lo = 0, hi = A.length; while (lo < hi) { const m = (lo + hi) >> 1; if (A[m] < x) lo = m + 1; else hi = m; } return lo; }
function ub(A, x) { let lo = 0, hi = A.length; while (lo < hi) { const m = (lo + hi) >> 1; if (A[m] <= x) lo = m + 1; else hi = m; } return lo; }

// Xin: reference scores (the bot's bank finals); kern: {A:[UB][L], B:[UB][L]} (rows sum to 1) or null; mUpF/mDnF: S -> margin; o.thinCap: IQR fraction for D_top/D_bot
function makeCtx(Xin, kern, mUpF, mDnF, o) {
  o = o || {};
  const X = Float64Array.from(Xin).sort(), N = X.length;
  const iqr = X[Math.min(N - 1, Math.floor(0.75 * N))] - X[Math.floor(0.25 * N)];
  const cap = (o.thinCap === undefined ? 0.5 : o.thinCap) * iqr;
  const Dtop = Math.min(X[N - 1] - X[N - 10], cap), Dbot = Math.min(X[9] - X[0], cap);
  const UB = kern ? kern.A.length : 0, L = kern ? kern.A[0].length : 0;
  return { X, N, Dtop, Dbot, mUp: mUpF, mDn: mDnF, iqr, kern, UB, L };
}
const quantile = (c, S) => (lb(c.X, S) + ub(c.X, S)) / (2 * c.N);
// kernel row at player score S: linear interpolation between adjacent player-quantile bin centres
function row(c, side, S) {
  const K = c.kern[side], UB = c.UB, L = c.L, pos = quantile(c, S) * UB - 0.5;
  let b0 = Math.floor(pos), lam = pos - b0; let b1 = b0 + 1;
  if (b0 < 0) { b0 = 0; b1 = 0; lam = 0; } if (b1 > UB - 1) { b1 = UB - 1; if (b0 > UB - 1) b0 = UB - 1; }
  const out = new Float64Array(L); const r0 = K[b0], r1 = K[b1];
  for (let l = 0; l < L; l++) out[l] = (1 - lam) * r0[l] + lam * r1[l];
  return out;
}
function invBin(w, v) { // inverse CDF over the position bins: [bin, fraction within bin]
  let acc = 0; const L = w.length;
  for (let l = 0; l < L; l++) { if (v < acc + w[l] || l === L - 1) { const fr = w[l] > 0 ? Math.min(0.999999, Math.max(0, (v - acc) / w[l])) : 0.5; return [l, fr]; } acc += w[l]; }
  return [L - 1, 0.5];
}
// ---- A side
function nbA(c, S, v, nA) { // honest min law over A(S): returns {val, j} (j = atom index, -1 when A(S) is empty: thin tail)
  const m = c.mUp(S), iA = lb(c.X, S + m), M = c.N - iA;
  const um = 1 - Math.pow(1 - v, 1 / nA); // S84 (D9): the thin tail uses the same min-law um as the atom case
  if (M <= 0) return { val: c5(S + m + um * c.Dtop), j: -1 };
  const j = iA + Math.min(M - 1, Math.floor(um * M));
  return { val: c.X[j], j };
}
function othA(c, S, nb, vp, w, wrow) {
  const X = c.X, N = c.N, j = nb.j;
  const M2 = j < 0 ? 0 : N - 1 - j;
  if (M2 <= 0) return c5(nb.val + 5 + vp * c.Dtop);
  const [l, fr] = invBin(wrow, vp), L = c.L;
  const lo = j + 1 + Math.floor(M2 * l / L), hi = Math.max(lo + 1, j + 1 + Math.floor(M2 * (l + 1) / L));
  const jj = Math.min(N - 1, lo + Math.floor(fr * (hi - lo)));
  const nx = jj + 1 < N ? X[jj + 1] : X[jj] + 40;
  return Math.max(c5(X[jj] + w * (nx - X[jj])), nb.val + 5);
}
// ---- B side (mirror)
function nbB(c, S, v, nB) {
  const m = c.mDn(S), iB = ub(c.X, S - m), M = iB;
  const um = 1 - Math.pow(1 - v, 1 / nB);
  if (M <= 0) return { val: Math.max(0, f5(S - m - um * c.Dbot)), j: -1 };
  const j = iB - 1 - Math.min(M - 1, Math.floor(um * M));
  return { val: c.X[j], j };
}
function othB(c, S, nb, vp, w, wrow) {
  const X = c.X, j = nb.j;
  const M2 = j < 0 ? 0 : j;
  if (M2 <= 0) return Math.max(0, f5(nb.val - 5 - vp * c.Dbot));
  const [l, fr] = invBin(wrow, vp), L = c.L;
  const hi = j - Math.floor(M2 * l / L), lo = Math.max(0, Math.min(hi - 1, j - Math.floor(M2 * (l + 1) / L)));
  const jj = Math.min(j - 1, lo + Math.floor((1 - fr) * (hi - lo)));
  const pv = jj > 0 ? X[jj - 1] : X[jj] - 40;
  return Math.max(0, Math.min(f5(X[jj] - w * (X[jj] - pv)), nb.val - 5));
}
const closeUp = (c, S, h) => c5(S + 20 + h * (c.mUp(S) - 20));
const closeDn = (c, S, h) => Math.max(0, f5(S - 20 - h * (c.mDn(S) - 20)));

// Targets for the Rivals of one round. spec: {close: 'up'|'dn'|null, h, A: {close, nb, others:[{i,vp,w}], vnb, nN}, B: {...}} (indices of Rival objects)
class Targets {
  constructor(c, spec) {
    this.c = c; this.spec = spec; this.cum = { A: [], B: [] }; this.order = { A: this._order('A'), B: this._order('B') };
    this.pos = {}; this.side = {};
    for (const sd of ['A', 'B']) this.order[sd].forEach((it, p) => { this.pos[it.i] = p; this.side[it.i] = sd; });
  }
  _order(side) { const s = this.spec[side]; const o = []; if (s.close >= 0) o.push({ i: s.close, kind: 'close' }); if (s.nb >= 0) o.push({ i: s.nb, kind: 'nb' }); for (const x of s.others) o.push({ i: x.i, kind: 'oth', vp: x.vp, w: x.w }); return o; }
  // the chain target of every Rival of `side` at grid score S (a multiple of 5): array parallel to this.order[side]
  chain(side, S) {
    const c = this.c, s = this.spec[side], ord = this.order[side], out = new Array(ord.length); const A = side === 'A';
    let prev = null, nbObj = null, wrow = null;
    for (let p = 0; p < ord.length; p++) {
      const it = ord[p]; let raw;
      if (it.kind === 'close') raw = A ? closeUp(c, S, this.spec.h) : closeDn(c, S, this.spec.h);
      else if (it.kind === 'nb') { nbObj = A ? nbA(c, S, s.vnb, s.nN) : nbB(c, S, s.vnb, s.nN); raw = nbObj.val; }
      else { if (!wrow) wrow = row(c, side, S); if (!nbObj) nbObj = { val: A ? S + c.mUp(S) : S - c.mDn(S), j: -1 }; raw = A ? othA(c, S, nbObj, it.vp, it.w, wrow) : othB(c, S, nbObj, it.vp, it.w, wrow); }
      let v = raw; if (prev !== null) v = A ? Math.max(raw, prev + 5) : Math.min(raw, prev - 5);
      if (!A && v < 0) v = 0;
      out[p] = v; prev = v;
    }
    return out;
  }
  // running-max target of Rival i at score S (A: grid up to ceil5(S); B: up to floor5(S))
  val(i, S) {
    const side = this.side[i]; if (side === undefined) return 0;
    const A = side === 'A', g = Math.max(0, A ? Math.ceil(S / 5 - 1e-9) : Math.floor(S / 5 + 1e-9)), cm = this.cum[side];
    while (cm.length <= g) {
      const gi = cm.length, ch = this.chain(side, 5 * gi), prev = gi ? cm[gi - 1] : null;
      cm.push(ch.map((v, q) => prev ? Math.max(prev[q], v) : v));
    }
    return cm[g][this.pos[i]];
  }
  // the raw (non-running-max) chain target at the exact grid point of S (audit / G5 x)
  raw(i, S) { const side = this.side[i]; const A = side === 'A'; const g = A ? Math.ceil(S / 5 - 1e-9) : Math.floor(S / 5 + 1e-9); return this.chain(side, 5 * g)[this.pos[i]]; }
}
module.exports = { f5, c5, lb, ub, makeCtx, quantile, row, invBin, nbA, othA, nbB, othB, closeUp, closeDn, Targets };
