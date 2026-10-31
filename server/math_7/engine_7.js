'use strict';
// engine_7.js — math_7 player engine (Rivals Classic, 10-place board; derived from engine_4.js). The math_3b engine, Classic only (Flash paths removed), physics and player side unchanged
// (so the math_3 bank reproduces). Empty starting jar, nominal spawns, jitter j_1. Adds tbRest() (tally base of landed bodies at rest, for S_lo) and payFor().
// Matter.js is injected. No fs/crypto/worker/DOM here.
const geom = require('./common/geom.js');
const rngm = require('./common/rng.js');
const { R } = geom;

function hex(u8) { let s = ''; for (let i = 0; i < u8.length; i++) s += (u8[i] < 16 ? '0' : '') + u8[i].toString(16); return s; }
// place 1..10 <-> rung id (places 6-10 are No Win; MATH_SPEC_6 1.1)
const PLACE_RUNG = [null, 'watermelon', 'melon', 'pineapple', 'peach', 'pear', 'nowin', 'nowin', 'nowin', 'nowin', 'nowin'];
const RUNG_PLACE = { watermelon: 1, melon: 2, pineapple: 3, peach: 4, pear: 5, nowin: 6 };

module.exports = function makeEngine(Matter, sha256, cfg, hashes) {
  const { Engine, Bodies, Body, Composite, Events, Common } = Matter;
  const P = cfg.physics, RU = cfg.rules, TL = cfg.tally;
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
      const self = this;
      Events.on(this.engine, 'collisionStart', e => { for (const p of e.pairs) self._pair(p, true); });
      Events.on(this.engine, 'collisionActive', e => { for (const p of e.pairs) self._pair(p, false); });
    }
    _pair(p, start) {
      const a = p.bodyA.ff, b = p.bodyB.ff;
      if (start) {
        if (a && b) { a.landed = true; b.landed = true; }
        else if (a && p.bodyB.label === 'floor') a.landed = true;
        else if (b && p.bodyA.label === 'floor') b.landed = true;
      }
      if (a && b && a.tier === b.tier && a.tier < 9) this.buf.push(a, b);
    }
    add(tier, x, y, o) {
      o = o || {};
      const body = Bodies.circle(x, y, R[tier], bodyOpts, P.maxSides);
      if (o.vx || o.vy) Body.setVelocity(body, { x: o.vx || 0, y: o.vy || 0 });
      const rec = { uid: this.uid++, tier, body, landed: !!o.landed, bornTick: o.bornTick === undefined ? -1 : o.bornTick, fromMerge: !!o.fromMerge, chainPos: o.chainPos || 0, dead: false };
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
    atRest() {
      for (const f of this.list) if (f.body.speed >= RU.restSpeed || f.body.angularSpeed >= RU.restAngSpeed) return false;
      return true;
    }
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
      this.o = o; this.mode = 'classic'; this.cfg = cfg;
      this.serverSeed = o.serverSeed; this.clientSeed = o.clientSeed; this.nonce = o.nonce;
      this.S = rngm.makeStreams(sha256, o.serverSeed, o.clientSeed, o.nonce);
      const x = this.S.draw.int(10000);
      this.drawnNatural = rngm.rungFromX(table, x);
      this.u = this.S.draw.float(); // tally target u (unchanged read, second draw read)
      this.u2 = this.S.draw.float(); // MATH_SPEC_6 1.2: the No Win place spread, ALWAYS read (three fixed draw reads in every round)
      this.drawnPlaceNatural = RUNG_PLACE[this.drawnNatural] === 6 ? 6 + Math.floor(5 * this.u2) : RUNG_PLACE[this.drawnNatural];
      this.place = o.forcedPlace || this.drawnPlaceNatural;
      this.rung = PLACE_RUNG[this.place];
      this.rating = o.rating || 1000;
      this.dropLimit = RU.classic.drops;
      this.w = new World(true);
      this.t = 0; this.drops = 0; this.ended = false; this.endReason = null;
      this.restCount = 0; this.ovCount = 0; this.overflowT = null;
      this.forgedMax = -1; this.markT = null; this.splay = 0;
      this.chainMerges = 0; this.merges = []; this.spawns = []; this.inputs = []; this.dropTicks = [];
      this.autoplay = { startT: null, drops: 0, active: false, nextT: 0 };
      this.lastInputT = 0; this.lastDropT = null; this.allowedAt = 0;
      this.pending = null; this.current = null; this.next = null;
      this.jMaxAbs = 0; this.spawnCount = [0, 0, 0, 0];
      this.bonus = null; this.bonusChecked = false;
      this.hooks = { jitter: (a, b, nt, x, y) => this._jitter(a, b, nt, x, y), merged: (rec, a, b, j, x, y) => this._merged(rec, a, b, j, x, y) };
      this.current = this._spawn(1); this.next = this._spawn(2);
      this.nspawn = 2;
    }
    get Ntot() { return this.dropLimit; }
    afterMark() {
      if (this.markT !== null) return true;
      const hit = this.drops >= RU.mark.classicDrop;
      if (hit) this.markT = this.t;
      return hit;
    }
    _spawn(n) {
      const f = this.S.spawn.float(); const tier = invCDF(nominal, f);
      this.spawnCount[tier]++;
      this.spawns.push([n, this.t, tier]);
      return tier;
    }
    // top of the highest landed body as a share of the overflow-line height (spec B.10.1)
    topH() {
      let top = P.jarH;
      for (const f of this.w.list) if (f.landed) { const y = f.body.position.y - R[f.tier]; if (y < top) top = y; }
      const h = (P.jarH - top) / (P.jarH - P.overflowY);
      return h < 0 ? 0 : h;
    }
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
      if (this.t < this.allowedAt) return false;
      return this.drops < this.dropLimit;
    }
    observe() {
      const o = { tick: this.t, mode: this.mode, canDrop: this.canDrop(), current: this.current, next: this.next, fruits: this.w.view(true) };
      o.dropsLeft = this.dropLimit - this.drops;
      return o;
    }
    _release(x) {
      const tier = this.current, r = R[tier];
      x = Math.min(Math.max(x, r + 1), P.jarW - r - 1);
      this.w.add(tier, x, P.dropY, { landed: false });
      this.drops++; this.lastDropT = this.t; this.dropTicks.push(this.t);
      this.allowedAt = this.t + RU.cooldownTicks; this.restCount = 0;
      this.current = this.next; this.next = null;
      this.pending = null;
      if (this.nspawn < this.Ntot) this.pending = { at: this.t + RU.nextDecisionDelay };
      this.afterMark();
      if (this.drops === RU.classic.checkDrop && !this.bonusChecked) {
        this.bonusChecked = true;
        if (this.o.bonusCheck && this.o.bonusCheck(this, 'classic')) { // bonus drops 19-21 (B.10.3)
          this.bonus = { kind: 'drops', t: this.t };
          this.dropLimit = RU.classic.drops + RU.classic.bonusDrops;
          this.current = this._spawn(this.nspawn + 1); this.nspawn++;
          this.pending = { at: this.t + RU.nextDecisionDelay };
        }
      }
      return x;
    }
    input(x) {
      if (!this.canDrop()) return false;
      const r = R[this.current]; x = Math.min(Math.max(x, r + 1), P.jarW - r - 1);
      this.inputs.push({ t: this.t, x }); // logged before the release so the bonus check can replay the input list
      this._release(x);
      this.lastInputT = this.t; this.autoplay.active = false;
      return true;
    }
    _autoDrop() {
      const view = this.w.view(false), c = this.current;
      let best = -1e18, bx = 300;
      for (const x of geom.colsCached(c, 25)) {
        const v = geom.repV(c, geom.features(c, x, view, false));
        if (v > best) { best = v; bx = x; }
      }
      bx += 8 * this.S.autoplay.gauss();
      const ax = this._release(bx);
      this.autoplay.drops++;
      this.autoplay.nextT = this.t + RU.classic.autoplayEveryTicks;
      return ax;
    }
    step() {
      if (this.ended) return;
      const t = this.t;
      this.afterMark();
      {
        const ap = this.autoplay, walk = RU.classic.walkAwayTicks;
        const left = this.drops < this.dropLimit;
        if (!ap.active && left && t - this.lastInputT >= walk) { ap.active = true; ap.startT = t; ap.nextT = t; }
        if (ap.active && left && t >= ap.nextT && this.canDrop()) this._autoDrop();
      }
      if (this.pending && t >= this.pending.at) {
        this.pending = null; this.nspawn++;
        this.next = this._spawn(this.nspawn);
      }
      let frozen = this.restCount >= RU.restTicks;
      let merged = 0;
      if (!frozen) { const m = this.w.step(this.hooks); merged = m.length; } else this.w.tick++;
      let over = false;
      for (const f of this.w.list) if (f.landed && f.body.position.y - R[f.tier] < P.overflowY) { over = true; break; }
      if (over) this.ovCount++; else this.ovCount = 0;
      if (!frozen) { if (merged === 0 && this.w.atRest()) this.restCount++; else this.restCount = 0; }
      this.t++;
      if (this.ovCount >= RU.overflowGraceTicks) { this.overflowT = this.t; this._finish('overflow'); return; }
      if (this.drops >= this.dropLimit && !this.pending) {
        if (this.restCount >= RU.restTicks || this.t >= this.lastDropT + RU.classic.settleCapTicks) this._finish('drops');
      }
    }
    _finish(reason) {
      this.ended = true; this.endReason = reason;
      let tb = 0;
      for (const f of this.w.list) tb += RU.tallyBase * Math.pow(2, f.tier);
      this.tallyBase = tb;
      this.overflowed = reason === 'overflow';
      const fs = finalScore(this.rating, this.u, this.place, this.splay, tb);
      this.c = fs.c; this.tally = fs.tally; this.Sfinal = fs.Sfinal; this.p = fs.p; this.pay = fs.pay;
      this.lastInputTick = this.inputs.length ? this.inputs[this.inputs.length - 1].t : 0;
      if (this.autoplay.drops && this.lastDropT !== null) this.lastInputTick = Math.max(this.lastInputTick, this.lastDropT);
    }
    // tally base of the landed bodies at rest (MATH_SPEC_4 1.4: S_lo(t) = P(t) + floor(0.85 * tbRest(t)))
    tbRest() {
      let tb = 0;
      for (const f of this.w.list) if (!f.dead && f.landed && f.body.speed < RU.restSpeed) tb += RU.tallyBase * Math.pow(2, f.tier);
      return tb;
    }
    // the tick of the last released fruit (player or autoplay): the end of input (spec B.4.5)
    result() {
      const endObj = { t: this.t, reason: this.endReason, forgedMax: this.forgedMax, Splay: this.splay, tallyBase: this.tallyBase, tally: this.tally, c: +this.c.toFixed(5), p: +this.p.toFixed(5),
        pay: +this.pay.toFixed(5), Sfinal: this.Sfinal, overflowT: this.overflowT, chainMerges: this.chainMerges, drops: this.drops };
      const eventHash = hex(sha256(rngm.utf8(JSON.stringify([this.spawns, this.merges, endObj, this.bonus]))));
      return { v: 7, math: 'math_7', engineHash: hashes.engine, configHash: hashes.config, mode: this.mode, bot: this.o.botName || null,
        serverSeed: this.serverSeed, clientSeed: this.clientSeed, nonce: this.nonce, drawnPlaceNatural: this.drawnPlaceNatural, place: this.place, u: +this.u.toFixed(6), u2: +this.u2.toFixed(6), rating: this.rating,
        mark: { t: this.markT }, inputs: this.inputs, spawns: this.spawns, merges: this.merges, autoplay: { startT: this.autoplay.startT, drops: this.autoplay.drops },
        bonus: this.bonus, end: endObj, eventHash, stateHash: this.w.stateHash() };
    }
  }
  return { World, Round, table, RUNG, finalScore, payFor, PLACE_RUNG, RUNG_PLACE, Matter };
};
module.exports.PLACE_RUNG = PLACE_RUNG;
module.exports.RUNG_PLACE = RUNG_PLACE;
