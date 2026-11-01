'use strict';
// engine_8.js — math_8 player engine (Rivals top-out; MATH_SPEC_8 on engine_7.js): no drop limit, the round ends at the block (overflow rule); ladder from config (geom.setRadii);
// pomegranate (tier code 10: never merges, bursts popDelay ticks after landing and pops up to popCap of the smallest touching fruit); regular pomegranate schedule from the `pom` stream (48 reads at init);
// rescue pull-ins (replaces bonus play); the mark = release n_m or the earlier first closing release; an exact fork lookahead at EVERY release (Round.fork, fork.js); fill clock A(t).
// Matter.js is injected. No fs/crypto/worker/DOM here.
const geom = require('./common/geom.js');
const rngm = require('./common/rng.js');
const { deepClone } = require('./fork.js');
const { R } = geom;

function hex(u8) { let s = ''; for (let i = 0; i < u8.length; i++) s += (u8[i] < 16 ? '0' : '') + u8[i].toString(16); return s; }
// place 1..10 <-> rung id (places 6-10 are No Win; MATH_SPEC_6 1.1)
const PLACE_RUNG = [null, 'watermelon', 'melon', 'pineapple', 'peach', 'pear', 'nowin', 'nowin', 'nowin', 'nowin', 'nowin'];
const RUNG_PLACE = { watermelon: 1, melon: 2, pineapple: 3, peach: 4, pear: 5, nowin: 6 };

module.exports = function makeEngine(Matter, sha256, cfg, hashes) {
  const { Engine, Bodies, Body, Composite, Events, Common } = Matter;
  const P = cfg.physics, RU = cfg.rules, TL = cfg.tally, PM = cfg.pom, RS = cfg.rescue;
  geom.setRadii(P.radii, PM.r);
  const AREA_DEN = P.jarW * (P.jarH - P.overflowY);
  const table = rngm.solveTable(cfg);
  const RUNG = {}; for (const r of cfg.rng.rungs) RUNG[r.id] = r;
  const nominal = RU.nominalSpawn;
  const bodyOpts = { restitution: P.restitution, friction: P.friction, frictionAir: P.frictionAir, frictionStatic: P.frictionStatic, density: P.density, slop: P.slop, label: 'fruit' };

  class World {
    constructor(resetIds) {
      if (resetIds) { Common._nextId = 0; Common._seed = 0; }
      this.engine = Engine.create({ gravity: P.gravity, positionIterations: P.positionIterations, velocityIterations: P.velocityIterations, constraintIterations: P.constraintIterations, enableSleeping: false });
      const wo = { isStatic: true, restitution: P.restitution, friction: P.friction };
      const t = P.wallThickness;
      const lw = Bodies.rectangle(-t / 2, 450, t, 2000, Object.assign({ label: 'wall' }, wo));
      const rw = Bodies.rectangle(P.jarW + t / 2, 450, t, 2000, Object.assign({ label: 'wall' }, wo));
      const fl = Bodies.rectangle(P.jarW / 2, P.jarH + t / 2, 800, t, Object.assign({ label: 'floor' }, wo));
      Composite.add(this.engine.world, [lw, rw, fl]);
      this.list = []; this.uid = 0; this.buf = []; this.tick = 0;
      this.bind();
    }
    bind() { // (re-)register the Matter handlers on THIS World (also after a fork copy)
      const self = this; this.engine.events = {};
      Events.on(this.engine, 'collisionStart', e => { for (const p of e.pairs) self._pair(p, true); });
      Events.on(this.engine, 'collisionActive', e => { for (const p of e.pairs) self._pair(p, false); });
    }
    _pair(p, start) {
      const a = p.bodyA.ff, b = p.bodyB.ff;
      if (start) {
        if (a && b) { a.landed = true; b.landed = true; if (a.tier === 10 && a.hitT === undefined) a.hitT = this.tick; if (b.tier === 10 && b.hitT === undefined) b.hitT = this.tick; }
        else if (a && p.bodyB.label === 'floor') { a.landed = true; if (a.tier === 10 && a.hitT === undefined) a.hitT = this.tick; }
        else if (b && p.bodyA.label === 'floor') { b.landed = true; if (b.tier === 10 && b.hitT === undefined) b.hitT = this.tick; }
      }
      if (a && b && a.tier === b.tier && a.tier < 9) this.buf.push(a, b);
    }
    add(tier, x, y, o) {
      o = o || {};
      const body = Bodies.circle(x, y, R[tier], bodyOpts, P.maxSides);
      if (o.vx || o.vy) Body.setVelocity(body, { x: o.vx || 0, y: o.vy || 0 });
      const rec = { uid: this.uid++, tier, body, landed: !!o.landed, hitT: undefined, bornTick: o.bornTick === undefined ? -1 : o.bornTick, fromMerge: !!o.fromMerge, chainPos: o.chainPos || 0, dead: false };
      body.ff = rec;
      Composite.add(this.engine.world, body);
      this.list.push(rec);
      return rec;
    }
    step(hooks) {
      this.buf.length = 0;
      Engine.update(this.engine, P.stepMs);
      const merges = [];
      if (this.buf.length) {
        const seen = new Set(), prs = [];
        for (let i = 0; i < this.buf.length; i += 2) {
          let a = this.buf[i], b = this.buf[i + 1];
          if (a.uid > b.uid) { const t = a; a = b; b = t; }
          const k = a.uid * 1048576 + b.uid;
          if (!seen.has(k)) { seen.add(k); prs.push([a, b]); }
        }
        prs.sort((p, q) => p[0].uid - q[0].uid || p[1].uid - q[1].uid);
        for (const [a, b] of prs) {
          if (a.dead || b.dead) continue;
          const nt = a.tier + 1, rn = R[nt];
          let x = (a.body.position.x + b.body.position.x) / 2, y = (a.body.position.y + b.body.position.y) / 2;
          x = Math.min(Math.max(x, rn), P.jarW - rn); y = Math.min(y, P.jarH - rn);
          const va = Body.getVelocity(a.body), vb = Body.getVelocity(b.body);
          a.dead = true; b.dead = true;
          const j = hooks && hooks.jitter ? hooks.jitter(a, b, nt, x, y) : 0;
          Composite.remove(this.engine.world, a.body); Composite.remove(this.engine.world, b.body);
          const rec = this.add(nt, x, y, { vx: (va.x + vb.x) / 2, vy: (va.y + vb.y) / 2 - P.pop * (1 + j), landed: true, bornTick: this.tick, fromMerge: true });
          merges.push(rec);
          if (hooks && hooks.merged) hooks.merged(rec, a, b, j, x, y);
        }
        if (merges.length) this.list = this.list.filter(f => !f.dead);
      }
      this.tick++;
      return merges;
    }
    view(withVel) {
      const out = [];
      for (let i = 0; i < this.list.length; i++) {
        const f = this.list[i], p = f.body.position;
        if (f.dead) continue;
        const o = { uid: f.uid, tier: f.tier, x: p.x, y: p.y, r: R[f.tier], landed: f.landed };
        if (withVel) { const v = Body.getVelocity(f.body); o.vx = v.x; o.vy = v.y; o.angle = f.body.angle; }
        out.push(o);
      }
      return out;
    }
    atRest() { // a pomegranate that has landed (it bursts <= popDelay ticks later) is excluded from the rest test; a falling one counts as moving
      for (const f of this.list) { if (f.tier === 10 && f.hitT !== undefined) continue; if (f.body.speed >= RU.restSpeed || f.body.angularSpeed >= RU.restAngSpeed) return false; }
      return true;
    }
    remove(rec) { rec.dead = true; Composite.remove(this.engine.world, rec.body); }
    stateHash() {
      const rows = this.list.slice().sort((a, b) => a.uid - b.uid).map(f => [f.uid, f.tier, f.body.position.x, f.body.position.y, f.body.angle, f.body.velocity.x, f.body.velocity.y].map(String).join(','));
      return hex(sha256(rngm.utf8(rows.join(';'))));
    }
  }

  function invCDF(Pv, f) { let acc = 0; for (let c = 0; c < 4; c++) { acc += Pv[c]; if (f < acc) return c; } return 3; }

  // final score (spec B.6.4): tally pulls S_final toward S* = r*exp(2w(u-0.5)); c in [cMin,cMax]; 6th place c is cosmetic.
  function finalScore(rating, u, place, Splay, TB) {
    const w = TL.w; let c;
    if (place <= 5) {
      const Sstar = rating * Math.exp(2 * w * (u - 0.5));
      const cRaw = TB > 0 ? (Sstar - Splay) / TB : TL.cMax;
      c = Math.min(TL.cMax, Math.max(TL.cMin, cRaw));
    } else c = TL.cMin + (TL.cMax - TL.cMin) * u;
    const tally = Math.round(c * TB), Sfinal = Splay + tally;
    const p = place <= 5 ? Math.min(1, Math.max(0, 0.5 + Math.log(Math.max(Sfinal, 1) / rating) / (2 * w))) : 0;
    const mult = RUNG[PLACE_RUNG[place]].mult;
    const pay = place <= 5 ? mult + 2 * cfg.rng.ramp * (p - cfg.rng.pCentre) : 0;
    return { c, tally, Sfinal, p, pay };
  }

  // in-rung p and the reward for a paid place (MATH_SPEC_4 3, 4): p from the score S (S_pay in bonus rounds), place 6 pays 0
  function payFor(rating, S, paidPlace) {
    const w = TL.w, p = Math.min(1, Math.max(0, 0.5 + Math.log(Math.max(S, 1) / rating) / (2 * w)));
    const mult = RUNG[PLACE_RUNG[paidPlace]].mult;
    return { p, pay: paidPlace <= 5 ? mult + 2 * cfg.rng.ramp * (p - cfg.rng.pCentre) : 0 };
  }

  class Round {
    constructor(o) {
      this.o = o; this.mode = 'topout'; this.cfg = cfg;
      this.serverSeed = o.serverSeed; this.clientSeed = o.clientSeed; this.nonce = o.nonce;
      this.S = rngm.makeStreams(sha256, o.serverSeed, o.clientSeed, o.nonce);
      const x = this.S.draw.int(10000);
      this.drawnNatural = rngm.rungFromX(table, x);
      this.u = this.S.draw.float(); // tally target u (second draw read)
      this.u2 = this.S.draw.float(); // MATH_SPEC_6 1.2: the No Win place spread, ALWAYS read (three fixed draw reads in every round)
      this.drawnPlaceNatural = RUNG_PLACE[this.drawnNatural] === 6 ? 6 + Math.floor(5 * this.u2) : RUNG_PLACE[this.drawnNatural];
      this.place = o.forcedPlace || this.drawnPlaceNatural;
      this.rung = PLACE_RUNG[this.place];
      this.rating = o.rating || 1000;
      // pomegranate regular schedule (MATH_SPEC_8 3.2): ALWAYS 48 reads from `pom` at init: gaps g_j = gapLo + int(gapHi - gapLo + 1); slots s_j = s_{j-1} + g_j. The same for every draw.
      this.pomGaps = []; this.pomSlots = []; { let sl = 0; for (let j = 0; j < PM.reads; j++) { const g = PM.gapLo + this.S.pom.int(PM.gapHi - PM.gapLo + 1); this.pomGaps.push(g); sl += g; this.pomSlots.push(sl); } }
      this.pomSet = new Set(this.pomSlots); this.regularSlots = new Set(this.pomSlots);
      this.escaped = 0; this.pomLog = []; this.pomReleased = []; this.pomPops = 0; // released pomegranates: {n, t, regular, pull}
      this.rescue = { flag: false, started: false, nr: -1, q: [], planned: [], pulls: 0, markEarly: false };
      this.w = new World(true);
      this.t = 0; this.drops = 0; this.ended = false; this.endReason = null;
      this.restCount = 0; this.ovCount = 0; this.overflowT = null;
      this.forgedMax = -1; this.markT = null; this.markN = null; this.splay = 0;
      this.areaMax = 0; this.areaNow = 0;
      this.chainMerges = 0; this.merges = []; this.spawns = []; this.inputs = []; this.dropTicks = [];
      this.autoplay = { startT: null, drops: 0, active: false, nextT: 0 };
      this.lastInputT = 0; this.lastDropT = null; this.allowedAt = 0;
      this.pending = null; this.current = null; this.next = null;
      this.jMaxAbs = 0; this.spawnCount = [0, 0, 0, 0];
      this.looks = []; this.forkTicks = []; this.isFork = false; this.pendLook = null;
      this._bindHooks();
      this.current = this._spawn(1); this.next = this._spawn(2);
      this.nspawn = 2;
    }
    _bindHooks() { this.hooks = { jitter: (a, b, nt, x, y) => this._jitter(a, b, nt, x, y), merged: (rec, a, b, j, x, y) => this._merged(rec, a, b, j, x, y) }; }
    _spawn(n) {
      const f = this.S.spawn.float(); let tier = invCDF(nominal, f); // the spawn read of a pomegranate slot is consumed and its tier discarded (MATH_SPEC_8 3.1)
      if (this.pomSet.has(n)) tier = 10; else this.spawnCount[tier]++;
      this.spawns.push([n, this.t, tier]);
      return tier;
    }
    // top of the highest landed body as a share of the overflow-line height (spec B.10.1); pomegranates excluded
    topH() {
      let top = P.jarH;
      for (const f of this.w.list) if (f.landed && f.tier !== 10) { const y = f.body.position.y - R[f.tier]; if (y < top) top = y; }
      const h = (P.jarH - top) / (P.jarH - P.overflowY);
      return h < 0 ? 0 : h;
    }
    // A(t): landed fruit area over the area below the line (MATH_SPEC_8 5.1); pomegranates excluded
    areaShare() { let a = 0; for (const f of this.w.list) if (!f.dead && f.landed && f.tier !== 10) a += Math.PI * R[f.tier] * R[f.tier]; return a / AREA_DEN; }
    _jitter() {
      const J = this.S.jitter, f0 = J.float(); J.float(); J.float(); // three draws consumed, j_1 used (math_2 stream layout)
      const j = -P.jitterBand + 2 * P.jitterBand * f0;
      this._lastJ = j; return j;
    }
    _merged(rec, a, b, j) {
      const t = this.t;
      let cp = 1;
      const wa = a.fromMerge && a.bornTick >= t - RU.chainWindowTicks, wb = b.fromMerge && b.bornTick >= t - RU.chainWindowTicks;
      if (wa || wb) cp = Math.max(wa ? a.chainPos : 0, wb ? b.chainPos : 0) + 1;
      rec.chainPos = cp;
      const pts = RU.pointBase * Math.pow(2, rec.tier) * Math.min(cp, RU.chainCap);
      this.splay += pts;
      if (cp >= 2) this.chainMerges++;
      if (rec.tier > this.forgedMax) this.forgedMax = rec.tier;
      if (Math.abs(j) > this.jMaxAbs) this.jMaxAbs = Math.abs(j);
      this.merges.push({ t, tier: rec.tier, a: a.uid, b: b.uid, new: rec.uid, j: +j.toFixed(5), chainPos: cp, pts });
    }
    canDrop() {
      if (this.ended || this.current === null) return false;
      return this.t >= this.allowedAt;
    }
    observe() {
      return { tick: this.t, mode: this.mode, canDrop: this.canDrop(), current: this.current, next: this.next, fruits: this.w.view(true) };
    }
    _release(x) {
      this._resolvePending(); // the previous release's look: the state just before this release
      const tier = this.current, r = R[tier];
      x = Math.min(Math.max(x, r + 1), P.jarW - r - 1);
      this.w.add(tier, x, P.dropY, { landed: false });
      this.drops++; this.lastDropT = this.t; this.dropTicks.push(this.t);
      if (tier === 10) { const sl = this.drops; this.pomReleased.push({ n: sl, t: this.t, regular: this.regularSlots.has(sl), pull: this.rescue.q.includes(sl) }); if (this.rescue.q.includes(sl)) this.rescue.pulls++; }
      this.allowedAt = this.t + RU.cooldownTicks; this.restCount = 0;
      this.current = this.next; this.next = null;
      this.pending = { at: this.t + RU.nextDecisionDelay };
      if (!this.isFork) this._onRelease();
      return x;
    }
    // ----- the fork lookahead (MATH_SPEC_8 5.4): a deep copy of this Round, run with no input and autoplay suppressed until it blocks (closing) / rests / reaches the next possible release
    fork() {
      const Cm = Matter.Common, sId = Cm._nextId, sSeed = Cm._seed;
      const H = ['o', 'looks', 'forkTicks', 'pendLook', 'merges', 'spawns', 'inputs', 'dropTicks', 'pomLog', 'pomReleased'], keep = {};
      for (const k of H) keep[k] = this[k];
      this.o = null; this.pendLook = null; for (const k of ['looks', 'forkTicks', 'merges', 'spawns', 'inputs', 'dropTicks', 'pomLog', 'pomReleased']) this[k] = []; // history is not copied (the fork never reads it)
      const f = deepClone(this);
      for (const k of H) this[k] = keep[k];
      f.o = {}; f.isFork = true; f.pendLook = null;
      f.w.bind(); f._bindHooks();
      Cm._nextId = sId; Cm._seed = sSeed;
      return f;
    }
    // The look of release n (MATH_SPEC_8 5.4): closing / S_n / Splay_n / h_inf / end state. EAGER: a fork (deep copy) run at the release. LAZY (default; identical results, checked by G12b): between releases the real round IS the no-input
    // continuation of the previous release, so the look is read off the real state when the real round blocks / rests / reaches the next possible release; if a release comes first, the state just before it is forked and run on.
    // Eager looks are used for releases before the mark (the early-block rule) and, in a flagged round, until the rescue episode has started (it needs h_inf at that release).
    _nextRelease() { const ap = this.autoplay; return ap.active ? Math.max(ap.nextT, this.allowedAt) : this.lastInputT + RU.walkAwayTicks; }
    _fillLook(lk, f, why) { // f = the Round holding the final state of the continuation (a fork, or this)
      let TB = 0;
      for (const q of f.w.list) if (!q.dead && q.tier !== 10) TB += RU.tallyBase * Math.pow(2, q.tier);
      let S;
      if (f.ended) { S = f.Sfinal; why = 'block'; TB = f.tallyBase; } else S = finalScore(f.rating, f.u, f.place, f.splay, TB).Sfinal;
      lk.S = S; lk.Splay = f.splay; lk.TB = TB; lk.closing = f.ended; lk.why = why; lk.h = f.topH(); lk.tEnd = f.ended ? f.t : -1; lk.hash = f.ended ? f.w.stateHash() : null; lk.fl = f.t - lk.t; lk.done = true;
      this.forkTicks.push(lk.fl);
    }
    _runFork(lk) { // fork the CURRENT state and run it with no input until it blocks / rests / reaches the next possible release
      const Cm = Matter.Common, sId = Cm._nextId, sSeed = Cm._seed;
      const f = this.fork(); const t0 = f.t, tNext = lk.tNext; let why = 'rest';
      while (!f.ended) {
        if (f.t >= tNext) { why = 'walk'; break; }
        if (f.restCount >= RU.restTicks && f.ovCount === 0) break;
        f.step();
        if (f.t - t0 > 40000) throw new Error('fork runaway');
      }
      Cm._nextId = sId; Cm._seed = sSeed;
      this._fillLook(lk, f, why);
    }
    _resolvePending() { if (this.pendLook) { const lk = this.pendLook; this.pendLook = null; this._runFork(lk); } }
    _checkPending() { // after a real step: has the real continuation reached the end of the pending look?
      const lk = this.pendLook; if (!lk) return;
      if (this.ended) { this.pendLook = null; this._fillLook(lk, this, 'block'); }
      else if (this.t >= lk.tNext) { this.pendLook = null; this._fillLook(lk, this, 'walk'); }
      else if (this.restCount >= RU.restTicks && this.ovCount === 0) { this.pendLook = null; this._fillLook(lk, this, 'rest'); }
    }
    flushLooks() { this._resolvePending(); }
    _onRelease() {
      const n = this.drops;
      if (this.o.noLook) { if (this.markT === null && n >= RU.mark.n) { this.markT = this.t; this.markN = n; } return; } // natural rounds (bank / ladder tuning): no Rival layer, no fork
      const lk = { t: this.t, n, S: null, Splay: null, TB: null, closing: null, why: null, h: null, tEnd: -1, hash: null, fl: null, tNext: this._nextRelease(), done: false };
      this.looks.push(lk);
      const eager = this.o.eagerLooks || n < RU.mark.n || (this.rescue.flag && !this.rescue.started && !this.rescue.markEarly);
      if (eager) this._runFork(lk); else this.pendLook = lk;
      if (this.markT === null && (n >= RU.mark.n || lk.closing)) { // MATH_SPEC_8 4.1-4.2: the mark = release n_m, or the earlier first closing release
        this.markT = this.t; this.markN = n; this.rescue.markEarly = n < RU.mark.n;
        if (this.o.rescueCheck && !this.o.noRescue) this.rescue.flag = !!this.o.rescueCheck(this);
      } else if (this.markT !== null && this.rescue.flag && !this.rescue.started && !this.rescue.markEarly && n > this.markN && !this.o.noRescue && lk.h >= cfg.clock.hLate) this._startRescue(n, lk);
    }
    // MATH_SPEC_8 3.3: one episode, <= 2 pull-ins. Slots <= n are released and slot n + 1 is the shown next, so the earliest changeable slot is n + 2.
    _startRescue(n, lk) {
      const RSC = this.rescue; RSC.started = true; RSC.nr = n; RSC.h = lk.h;
      const sl = this.pomSlots.slice(), gaps = this.pomGaps;
      let sPrev = 0; for (const v of sl) if (v <= n + 1) sPrev = v;
      let j1 = sl.findIndex(v => v > n + 1); if (j1 < 0) return;
      const q1 = Math.max(n + 2, sPrev + RS.gap);
      sl[j1] = Math.min(sl[j1], q1);
      if (RS.pulls >= 2 && j1 + 1 < sl.length) sl[j1 + 1] = sl[j1] + RS.gap;
      for (let j = j1 + 2; j < sl.length; j++) sl[j] = sl[j - 1] + gaps[j];
      RSC.q = [];
      for (let j = j1; j <= j1 + (RS.pulls >= 2 ? 1 : 0) && j < sl.length; j++) if (sl[j] !== this.pomSlots[j]) RSC.q.push(sl[j]);
      RSC.planned = RSC.q.slice();
      this.pomSlots = sl; this.pomSet = new Set(sl);
    }
    input(x) {
      if (!this.canDrop()) return false;
      const r = R[this.current]; x = Math.min(Math.max(x, r + 1), P.jarW - r - 1);
      this.inputs.push({ t: this.t, x });
      this.lastInputT = this.t; this.autoplay.active = false; // set BEFORE the release: the fork lookahead of this release reads them
      this._release(x);
      return true;
    }
    _autoDrop() {
      const view = this.w.view(false), c = this.current;
      let bx;
      if (c === 10) bx = geom.pomAim(view, false);
      else {
        let best = -1e18; bx = 300;
        for (const x of geom.colsCached(c, 25)) {
          const v = geom.repV(c, geom.features(c, x, view, false));
          if (v > best) { best = v; bx = x; }
        }
      }
      bx += 8 * this.S.autoplay.gauss();
      this.autoplay.drops++;
      this.autoplay.nextT = this.t + RU.autoplayEveryTicks; // before the release (the fork reads it)
      return this._release(bx);
    }
    // a body that has been pushed through a wall or the floor (centre outside the jar by more than the margin) is lost: removed at once, scores nothing, leaves the tally. Counted (U53).
    _escapes() {
      const w = this.w; let any = false;
      for (const f of w.list) { if (f.dead) continue; const p = f.body.position; if (p.x < -P.escapeMargin || p.x > P.jarW + P.escapeMargin || p.y > P.jarH + P.escapeMargin) { w.remove(f); this.escaped++; any = true; } }
      if (any) w.list = w.list.filter(f => !f.dead);
    }
    _bursts() { // MATH_SPEC_8 3.1: popDelay ticks after the first landing, the pomegranate and up to popCap of the smallest touching Cherry/Strawberry/Grape are removed in the same tick
      const w = this.w;
      for (const rec of w.list.slice()) {
        if (rec.tier !== 10 || rec.dead || rec.hitT === undefined || w.tick - 1 < rec.hitT + PM.popDelay) continue;
        const px = rec.body.position.x, py = rec.body.position.y, c = [];
        for (const f of w.list) {
          if (f.dead || f.tier === 10 || f.tier > PM.popTierMax) continue;
          const dx = f.body.position.x - px, dy = f.body.position.y - py, s = PM.r + R[f.tier] + 4;
          if (dx * dx + dy * dy <= s * s) c.push(f);
        }
        c.sort((a, b) => a.tier - b.tier || a.uid - b.uid);
        const pop = c.slice(0, PM.popCap);
        for (const f of pop) w.remove(f);
        w.remove(rec); w.list = w.list.filter(f => !f.dead);
        this.pomPops += pop.length; this.pomLog.push({ t: this.t, uid: rec.uid, pops: pop.map(f => [f.uid, f.tier]) });
      }
    }
    step() {
      if (this.ended) return;
      const t = this.t;
      if (!this.isFork) {
        const ap = this.autoplay, walk = RU.walkAwayTicks;
        if (!ap.active && t - this.lastInputT >= walk) { ap.active = true; ap.startT = t; ap.nextT = t; }
        if (ap.active && t >= ap.nextT && this.canDrop()) this._autoDrop();
      }
      if (this.pending && t >= this.pending.at) {
        this.pending = null; this.nspawn++;
        this.next = this._spawn(this.nspawn);
      }
      let frozen = this.restCount >= RU.restTicks;
      let merged = 0;
      if (!frozen) { const m = this.w.step(this.hooks); merged = m.length; } else this.w.tick++;
      if (!frozen) { this._escapes(); this._bursts(); const a = this.areaShare(); this.areaNow = a; if (a > this.areaMax) this.areaMax = a; }
      let over = false;
      for (const f of this.w.list) if (f.tier !== 10 && f.landed && f.body.position.y - R[f.tier] < P.overflowY) { over = true; break; }
      if (over) this.ovCount++; else this.ovCount = 0;
      if (!frozen) { if (merged === 0 && this.w.atRest()) this.restCount++; else this.restCount = 0; }
      this.t++;
      if (this.ovCount >= RU.overflowGraceTicks) { this.overflowT = this.t; this._finish('block'); }
      if (this.pendLook) this._checkPending();
    }
    _finish(reason) {
      this.ended = true; this.endReason = reason;
      let tb = 0;
      for (const f of this.w.list) if (f.tier !== 10) tb += RU.tallyBase * Math.pow(2, f.tier);
      this.tallyBase = tb;
      this.blocked = reason === 'block';
      const fs = finalScore(this.rating, this.u, this.place, this.splay, tb);
      this.c = fs.c; this.tally = fs.tally; this.Sfinal = fs.Sfinal; this.p = fs.p; this.pay = fs.pay;
      this.lastInputTick = this.inputs.length ? this.inputs[this.inputs.length - 1].t : 0;
      if (this.autoplay.drops && this.lastDropT !== null) this.lastInputTick = Math.max(this.lastInputTick, this.lastDropT);
    }
    // tally base of the landed bodies at rest (MATH_SPEC_4 1.4: S_lo(t) = P(t) + floor(0.85 * tbRest(t))); pomegranates contribute 0
    tbRest() {
      let tb = 0;
      for (const f of this.w.list) if (!f.dead && f.tier !== 10 && f.landed && f.body.speed < RU.restSpeed) tb += RU.tallyBase * Math.pow(2, f.tier);
      return tb;
    }
    result() {
      const endObj = { t: this.t, reason: this.endReason, forgedMax: this.forgedMax, Splay: this.splay, tallyBase: this.tallyBase, tally: this.tally, c: +this.c.toFixed(5), p: +this.p.toFixed(5),
        pay: +this.pay.toFixed(5), Sfinal: this.Sfinal, overflowT: this.overflowT, chainMerges: this.chainMerges, drops: this.drops };
      const eventHash = hex(sha256(rngm.utf8(JSON.stringify([this.spawns, this.merges, endObj, this.pomLog, this.rescue]))));
      return { v: 8, math: 'math_8', engineHash: hashes.engine, configHash: hashes.config, mode: this.mode, bot: this.o.botName || null,
        serverSeed: this.serverSeed, clientSeed: this.clientSeed, nonce: this.nonce, drawnPlaceNatural: this.drawnPlaceNatural, place: this.place, u: +this.u.toFixed(6), u2: +this.u2.toFixed(6), rating: this.rating,
        mark: { t: this.markT, n: this.markN }, inputs: this.inputs, spawns: this.spawns, merges: this.merges, autoplay: { startT: this.autoplay.startT, drops: this.autoplay.drops },
        pom: { log: this.pomLog, released: this.pomReleased, rescue: this.rescue, slots: this.pomSlots.slice(0, 24) }, end: endObj, eventHash, stateHash: this.w.stateHash() };
    }
  }
  return { World, Round, table, RUNG, finalScore, payFor, PLACE_RUNG, RUNG_PLACE, Matter };
};
module.exports.PLACE_RUNG = PLACE_RUNG;
module.exports.RUNG_PLACE = RUNG_PLACE;
