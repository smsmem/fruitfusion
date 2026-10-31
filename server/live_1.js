'use strict';
// live_1.js: the causal live driver of the math_7 round (build code, not math). It ports, without changing any rule:
//   harness_7.js lookaheadN (lines 67-92), makeLooks (96-128), streamsOf (130), simulate (133-195) and boardHash (197-203).
// FF.lookTools(env)  : look work, run in Worker 2 (or inline in Node): lookaheadN and the forward replay of a round to its end.
// FF.Live            : the live round, run in Worker 1 (or in Node): one tick at a time, looks requested at the same events as makeLooks,
//                      the relook trigger evaluated causally, Rival snapshots published only when every look with l.t <= s is resolved.
(function (G) {
  const FF = G.FF = G.FF || {};

  // ---------------------------------------------------------------- look tools (Worker 2)
  FF.lookTools = function (env) {
    const cfg = env.cfg, E = env.E, Matter = env.Matter, Cm = Matter.Common;
    // harness_7.js lookaheadN, lines 67-92 (round = {o, inputs}); env.* as in the harness
    function lookaheadN(round, n, opt) {
      opt = opt || {};
      const RU = cfg.rules, HZ = cfg.board.lookHorizon, sId = Cm._nextId, sSeed = Cm._seed;
      const r2 = new E.Round(Object.assign({}, round.o, { bonusCheck: opt.bonus ? () => true : null }));
      const rec = opt.record ? { Pt: [], TB: [] } : null;
      const inp = round.inputs; let k = 0, held = false, tCut = Infinity;
      const natural = opt.atTick === undefined && n >= cfg.rules.classic.drops && !opt.bonus;
      const hold = () => {
        if (held || natural) return;
        if (opt.atTick !== undefined ? r2.t > opt.atTick : r2.dropTicks.length >= n) { held = true; r2.autoplay.active = false; r2.lastInputT = Infinity; tCut = opt.atTick !== undefined ? opt.atTick : r2.dropTicks[n - 1]; }
      };
      while (!r2.ended) {
        hold();
        if (held && (r2.restCount >= RU.restTicks || r2.t >= tCut + HZ)) break;
        if (rec) { rec.Pt.push(r2.splay); rec.TB.push(r2.tbRest()); }
        if (!held) { while (k < inp.length && inp[k].t === r2.t) { r2.input(inp[k].x); k++; } hold(); }
        r2.step();
        if (r2.t > 30000) throw new Error('lookahead runaway');
      }
      let S;
      if (r2.ended) S = r2.Sfinal;
      else { let tb = 0; for (const f of r2.w.list) tb += RU.tallyBase * Math.pow(2, f.tier); S = E.finalScore(r2.rating, r2.u, r2.place, r2.splay, tb).Sfinal; }
      const len = tCut === Infinity ? 0 : r2.t - tCut;
      Cm._nextId = sId; Cm._seed = sSeed;
      return { S, r2, rec, len, hitHorizon: held && !r2.ended && r2.restCount < RU.restTicks };
    }
    // a look request -> a serializable answer
    function runLook(q) {
      const lk = lookaheadN({ o: q.o, inputs: q.inputs }, q.n, { bonus: q.bonus, record: q.record, atTick: q.atTick });
      const out = { S: lk.S };
      if (q.record) { const r2 = lk.r2; out.nb = { S: lk.S, fin2: { Sfinal: r2.Sfinal, tEnd: r2.t, overflow: r2.overflowed, lastDropT: r2.lastDropT }, dropTicks: r2.dropTicks.slice(), Pt: lk.rec.Pt, TB: lk.rec.TB }; }
      return out;
    }
    // the forward replay of the round from its logged inputs to its end (the same Round options; the bonus decision is the live one)
    function forward(o, inputs, bonusFires) {
      const sId = Cm._nextId, sSeed = Cm._seed;
      const r = new E.Round(Object.assign({}, o, { bonusCheck: () => bonusFires }));
      const Pt = [], Ht = [], TB = []; let ip = 0;
      while (!r.ended) {
        Pt.push(r.splay); Ht.push(r.markT === null ? r.topH() : 0); TB.push(r.tbRest());
        while (ip < inputs.length && inputs[ip].t === r.t) { if (!r.input(inputs[ip].x)) throw new Error('forward replay: input rejected at t=' + r.t); ip++; }
        r.step();
        if (r.t > 30000) throw new Error('forward replay runaway');
      }
      if (ip < inputs.length) throw new Error('forward replay: unused inputs');
      const res = r.result();
      Cm._nextId = sId; Cm._seed = sSeed;
      return { Pt, Ht, TB, dropTicks: r.dropTicks.slice(), markT: r.markT, fin: { Sfinal: r.Sfinal, tEnd: r.t, overflow: r.overflowed, lastDropT: r.lastDropT === null ? 0 : r.lastDropT }, stateHash: res.stateHash, eventHash: res.eventHash, endReason: r.endReason };
    }
    return { lookaheadN, runLook, forward };
  };

  // ---------------------------------------------------------------- boardHash (harness_7.js 197-203)
  function boardHash(env, brd, fin, looks) {
    const sha256 = env.sha256, hexs = env.hexs, enc = new TextEncoder();
    const ev = brd.events.map(e => [e.t, e.i, e.before, e.after]);
    const al = brd.alerts.map(a => [a.j, a.rival, a.state, a.t]);
    const h = brd.riv.map(r => [r.handle, r.icon, r.R, r.drops]);
    const mi = brd.markInfo;
    return hexs(sha256(enc.encode(JSON.stringify([h, ev, al, mi && [mi.t, mi.rank, mi.A, mi.frozen, mi.bonus, mi.v, mi.w, mi.z, mi.y, mi.L, mi.leaders, mi.flag.side, mi.flag.h], fin.Sfinal, brd.tClose, (looks || []).map(l => [l.t, l.n, l.S, l.final])]))));
  }
  FF.boardHash = boardHash;

  // ---------------------------------------------------------------- the live round (Worker 1)
  // io: {emit(msg), look(q), replay(q), work(q), now()}; answers come back through live.onLook / onReplay / onWork. nothing here is visible to the client except what emit() gets.
  class Live {
    constructor(env, opt, io) {
      this.env = env; this.io = io; this.cfg = env.cfg; this.RV = env.RV; this.E = env.E; this.test = !!opt.test;
      const cfg = this.cfg;
      this.base = { mode: 'classic', serverSeed: opt.serverSeed, clientSeed: opt.clientSeed, nonce: opt.nonce, forcedPlace: opt.forcedPlace || null, rating: opt.rating, botName: null };
      this.tr = { Pt: [], Ht: [], TB: [], dropTicks: null, tMark: null, looks: [] };
      this.bonusEval = [];
      const self = this;
      const bonusCheck = round => { // simulate()'s bonusCheck (harness 141-148); runBoard runs in every round (constant work), the place test is applied to its result
        const rec = { t: round.t, place: round.place, markT: round.markT, fired: false };
        self.bonusEval.push(rec);
        if (round.markT === null) return false;
        const brd = self.RV.runBoard(self.mkPar(), self.streamsOf(), { Pt: self.tr.Pt, Ht: self.tr.Ht, TB: self.tr.TB, dropTicks: round.dropTicks, tMark: round.markT, looks: [] }, round.markT, null);
        rec.fired = round.place <= cfg.board.bonus.kMax && !!(brd.markInfo && brd.markInfo.bonus);
        return rec.fired;
      };
      this.r = new this.E.Round(Object.assign({}, this.base, { bonusCheck }));
      this.tr.dropTicks = this.r.dropTicks;
      this.mxy = []; { const r = this.r, hm = r.hooks.merged; r.hooks.merged = (rec, a, b, j, x, y) => { hm(rec, a, b, j, x, y); self.mxy.push([x, y]); }; }
      this.T = 0; this.nextId = 1;
      this.looks = []; this.pend = new Map(); this.lookTicks = new Set(); this.workPend = 0;
      this.slo = []; this.sloMax = 0; this.sc = null; this.scanDone = false; this.guard = 0;
      this.limitTau = null; this.limitN = 0; this.fin = null; this.ftrace = null; this.liveEnd = null; this.replay = null; this.nb = null; this.final = null;
      this.queue = []; this.sPrev = -1; this.popCursor = 0; this.lastKey = null; this.lastAlertCount = 0; this.published = []; this.alertLog = []; this.shownAlerts = new Set();
      this.tally = null; this.finSent = false; this.bonusSent = false; this.done = false; this.errors = []; this.holdMs = []; this.dueAt = new Map(); this.snapRecords = [];
      this.pendingX = null; this.finalMsg = null; this.log = null; this.phSent = 'play';
    }
    mkPar() { return { cfg: this.cfg, bank: this.env.bank, kern: this.env.kern, bot: 'rep', place: this.r.place, rating: this.base.rating }; }
    streamsOf() { const b = this.base, s = this.env.rngm.makeStreams(this.env.sha256, b.serverSeed, b.clientSeed, b.nonce); return { board: s.board, rival: s.rival, alert: s.alert }; }
    fail(m) { this.errors.push(m); if (this.test) throw new Error(m); }
    get busy() { return this.pend.size + this.workPend + (this.replayPend ? 1 : 0); }

    // ---- one server tick (x: the queued player drop, or null)
    tick(x) {
      const r = this.r, cfg = this.cfg, tr = this.tr;
      let frameT = this.T, mg = [], ended0 = r.ended;
      const nd0 = r.dropTicks.length, nm0 = r.merges.length, bonus0 = r.bonus;
      if (!r.ended) {
        const t = r.t;
        tr.Pt.push(r.splay); tr.Ht.push(r.markT === null ? r.topH() : 0); tr.TB.push(r.tbRest());
        this.sloMax = Math.max(this.sloMax, tr.Pt[t] + Math.floor(cfg.board.sloFrac * (tr.TB[t] || 0))); this.slo[t] = this.sloMax;
        if (x !== null && x !== undefined && !r.input(x)) this.io.emit({ k: 'rej' });
        r.step();
        if (r.markT !== null) tr.tMark = r.markT;
        for (let i = nm0; i < r.merges.length; i++) { const m = r.merges[i], p = this.mxy[i]; mg.push([m.tier, p[0], p[1], m.chainPos]); }
      } else if (x !== null && x !== undefined) this.io.emit({ k: 'rej' });
      if (!ended0 && r.bonus && !bonus0) this.io.emit({ k: 'bonus', t: frameT, dl: r.dropLimit - r.drops }); // before the frame that carries the new drops-left
      // frame
      const fr = r.w.view(true).map(f => [f.uid, f.tier, f.x, f.y, f.angle]);
      this.io.emit({ k: 'f', t: frameT, fr, cur: ended0 ? null : r.current, nxt: ended0 ? null : r.next, can: r.canDrop(), cd: Math.max(0, r.allowedAt - r.t), dl: ended0 ? 0 : r.dropLimit - r.drops, ap: r.autoplay.active, mg, ov: r.ovCount > 0 });
      if (!ended0) {
        const nd = r.dropTicks.length;
        if (nd > nd0) this.onDrop(nd, r.dropTicks[nd - 1]);
        if (r.ended) this.onLiveEnd();
        this.scan();
      }
      // snapshot due at this tick: s = T - 1
      const s = this.T - 1;
      if (s >= 0 && this.isDue(s)) this.due(s);
      this.T++;
      this.processSnaps();
    }
    isDue(s) {
      if (s === 0 || s % 6 === 5) return true;
      if (this.liveEnd) { const te = this.liveEnd.tEnd; if (s === te - 1 || s === te) return true; if (s === this.tClose()) return true; }
      return false;
    }
    tClose() { const f = this.fin || this.liveEnd; const B = this.cfg.board; return f.tEnd + (f.overflow ? B.playoutTicks : B.closeTicksClassic); }
    due(s) {
      if (this.queue.indexOf(s) >= 0) return;
      this.queue.push(s); this.dueAt.set(s, this.io.now());
    }

    // ---- looks (makeLooks, event by event)
    newId() { return this.nextId++; }
    requestLook(t, n, extra) { // a look at tick t for drop n (n = 0: a relook)
      const id = this.newId(); this.pend.set(id, { t, n }); this.lookTicks.add(t);
      this.io.look(Object.assign({ id, o: this.optsForLook(), inputs: this.r.inputs.map(i => ({ t: i.t, x: i.x })), n }, extra));
    }
    optsForLook() { const b = this.base; return { mode: b.mode, serverSeed: b.serverSeed, clientSeed: b.clientSeed, nonce: b.nonce, forcedPlace: b.forcedPlace, rating: b.rating, botName: b.botName }; }
    requestWork() { this.workPend++; this.io.work({ id: this.newId(), o: this.optsForLook(), inputs: this.r.inputs.map(i => ({ t: i.t, x: i.x })), n: 18 }); }
    onDrop(n, tau) {
      const r = this.r, from = this.cfg.board.lookFromDrop;
      if (n < from) return;
      if (n === r.dropLimit) { // the last drop by limit: the forward replay gives the exact end
        this.limitTau = tau; this.limitN = n; this.replayPend = true;
        this.io.replay({ id: this.newId(), o: this.optsForLook(), inputs: r.inputs.map(i => ({ t: i.t, x: i.x })), bonusFires: r.bonus !== null });
      } else if (n === 18 && r.bonus) this.requestLook(tau, 18, { bonus: false, record: true });
      else this.requestLook(tau, n, { bonus: n >= 19 });
    }
    onLook(id, res) {
      const p = this.pend.get(id); if (!p) return;
      this.pend.delete(id);
      this.looks.push({ t: p.t, n: p.n, S: res.S, final: false }); this.sortLooks();
      if (res.nb) this.nb = res.nb;
      this.afterResult();
    }
    onWork() { this.workPend--; this.afterResult(); }
    sortLooks() { this.looks.sort((x, y) => x.t - y.t || (x.final ? 1 : -1)); }
    onReplay(res) {
      this.replayPend = false; this.replay = res;
      const r = this.r;
      if (r.ended) this.checkReplay();
      this.setFin(res.fin, { Pt: res.Pt, Ht: res.Ht, TB: res.TB, dropTicks: res.dropTicks, markT: res.markT });
      // extend S_lo beyond the live progress (needed only by overflow tails)
      const SF = this.cfg.board.sloFrac;
      for (let t = this.slo.length; t < res.Pt.length; t++) { this.sloMax = Math.max(this.sloMax, res.Pt[t] + Math.floor(SF * (res.TB[t] || 0))); this.slo[t] = this.sloMax; }
      if (res.fin.overflow) this.requestLook(this.limitTau, this.limitN, { bonus: this.limitN >= 19 });
      if (r.bonus === null) this.requestWork();
      this.afterResult();
    }
    checkReplay() { // t_End: the live round must equal the forward replay
      const r = this.r, rp = this.replay, res = r.result();
      if (rp.fin.Sfinal !== r.Sfinal || rp.fin.tEnd !== r.t || rp.stateHash !== res.stateHash || rp.eventHash !== res.eventHash) this.fail('live round differs from the forward replay (Sfinal ' + r.Sfinal + '/' + rp.fin.Sfinal + ', tEnd ' + r.t + '/' + rp.fin.tEnd + ')');
    }
    onLiveEnd() {
      const r = this.r;
      this.liveEnd = { Sfinal: r.Sfinal, tEnd: r.t, overflow: r.overflowed, lastDropT: r.lastDropT === null ? 0 : r.lastDropT };
      this.io.emit({ k: 'end', t: r.t, reason: r.endReason === 'overflow' ? 'overflow' : 'drops' });
      if (this.limitTau === null) { // ended before its last drop: the live values are the end
        this.setFin(Object.assign({}, this.liveEnd), { Pt: this.tr.Pt, Ht: this.tr.Ht, TB: this.tr.TB, dropTicks: r.dropTicks, markT: r.markT });
        if (r.bonus && !this.nb) this.requestLook(r.dropTicks[17], 18, { bonus: false, record: true }); // harness 108 (never reached: a bonus round always passes drop 18)
        else if (!r.bonus) this.requestWork();
        else this.afterResult(); // rev 1: a bonus round that overflows before its drop limit has its bonus look resolved already; nothing else will call tryFinal (rev 0 left such a round without a result)
      } else if (this.replay) this.checkReplay();
    }
    setFin(fin, trace) {
      this.fin = fin; this.ftrace = trace;
      const D = trace.dropTicks.length, tFinal = fin.overflow ? fin.tEnd : fin.lastDropT;
      this.looks.push({ t: tFinal, n: D, S: fin.Sfinal, final: true }); this.sortLooks(); this.lookTicks.add(tFinal);
    }
    afterResult() { this.scan(); this.tryFinal(); this.processSnaps(); }

    // ---- the relook trigger (makeLooks lines 113-126), evaluated causally
    scan() {
      const d = this.r.dropTicks, B = this.cfg.board;
      if (this.scanDone || d.length < B.lookFromDrop) return;
      if (this.sc === null) this.sc = d[B.lookFromDrop - 1];
      for (;;) {
        const t = this.sc;
        if (this.guard >= B.maxRelooks) { this.scanDone = true; return; }
        let lim = Infinity;
        if (this.fin) lim = this.fin.overflow ? this.fin.tEnd : this.fin.lastDropT; else if (this.limitTau !== null) lim = this.limitTau;
        if (t >= lim) { if (this.fin) this.scanDone = true; return; }
        if (t >= this.slo.length) return;
        for (const p of this.pend.values()) if (p.t <= t) return;
        let last = null; for (const l of this.looks) if (l.t <= t) last = l;
        if (last && !last.final && this.slo[t] > last.S && !this.lookTicks.has(t)) { this.requestLook(t, 0, { atTick: t }); this.guard++; }
        this.sc++;
      }
    }

    // ---- the final board (once fin is known and every look is resolved)
    tryFinal() {
      if (this.final || !this.fin) return;
      const need = this.r.dropTicks.length >= this.cfg.board.lookFromDrop;
      if ((need && !this.scanDone) || this.pend.size) return;
      const ft = this.ftrace, tr = { Pt: ft.Pt, Ht: ft.Ht, TB: ft.TB, dropTicks: ft.dropTicks, tMark: ft.markT, looks: this.looks.map(l => Object.assign({}, l)) };
      this.finalTrace = tr;
      this.final = this.RV.runBoard(this.mkPar(), this.streamsOf(), tr, null, this.fin);
    }
    tStart() { if (this.fin && this.liveEnd && this.limitTau === null) return this.liveEnd.tEnd; return this.limitTau !== null ? this.limitTau : Infinity; }
    canServe(s) {
      const d = this.r.dropTicks, B = this.cfg.board;
      if (s < this.tStart()) {
        if (d.length >= B.lookFromDrop && d[B.lookFromDrop - 1] <= s) {
          if (!(this.scanDone || this.sc > s)) return false;
          for (const p of this.pend.values()) if (p.t <= s) return false;
        }
        return true;
      }
      return !!this.final;
    }

    // ---- snapshots (the only Rival data the client gets)
    processSnaps() {
      while (this.queue.length) {
        const s = this.queue[0];
        if (!this.canServe(s)) break;
        this.queue.shift();
        this.publish(s);
      }
    }
    publish(s) {
      const r = this.r, RV = this.RV, B = this.cfg.board;
      let brd, P, partial = false;
      if (s < this.tStart()) {
        const tr = { Pt: this.tr.Pt, Ht: this.tr.Ht, TB: this.tr.TB, dropTicks: r.dropTicks, tMark: r.markT, looks: this.looks.filter(l => l.t <= s) };
        brd = RV.runBoard(this.mkPar(), this.streamsOf(), tr, s, null); partial = true;
      } else brd = this.final;
      P = brd.Pof(s);
      const R = brd.riv.map(v => brd.Rt[v.i][s]);
      const fin = this.fin || this.liveEnd, ovf = !!(fin && fin.overflow && s >= fin.tEnd); // rev 1 (S1): overflow playout = display rule only; the engine and the final run are unchanged
      const ovfEmit = ovf && s === fin.tEnd;
      if (this.test) this.snapRecords.push({ s, P: ovfEmit ? r.splay : P, R: ovfEmit ? null : R.slice(), partial, pub: !(ovf && !ovfEmit), ovfEnd: ovfEmit, Pev: P, Rev: R.slice() });
      if (ovf) {
        const pops = []; for (let i = 0; i < r.merges.length; i++) { const m = r.merges[i]; if (m.t >= this.popCursor && m.t < s) pops.push([this.mxy[i][0], this.mxy[i][1], m.pts]); }
        this.popCursor = Math.max(this.popCursor, s); this.sPrev = s;
        if (ovfEmit) { // exactly one overflow-end message: no rows, no header, P = the player's merge score, no tally (everything from here to final is a function of the player's own play only)
          this.lastKey = 'ovf'; this.phSent = 'fin';
          this.published.push([s, r.splay, null]);
          this.io.emit({ k: 'b', s, P: r.splay, header: '', rows: [], al: [], pops, ph: 'fin' });
          const t0 = this.dueAt.get(s); if (t0 !== undefined) this.holdMs.push(this.io.now() - t0);
        }
        if (s === this.tClose()) this.finish();
        return;
      }
      const view = RV.boardView({ P, rivals: brd.riv.map(v => ({ i: v.i, handle: v.handle, R: brd.Rt[v.i][s] })) }, B.places);
      const al = brd.alerts.filter(a => a.state === 'fired' && a.t > this.sPrev && a.t <= s).map(a => brd.riv[a.rival].handle);
      for (const a of brd.alerts) if (a.state === 'fired' && a.t > this.sPrev && a.t <= s) this.alertLog.push([a.t, brd.riv[a.rival].handle]);
      const ph = fin && s >= fin.tEnd ? 'fin' : 'play';
      const pops = []; for (let i = 0; i < r.merges.length; i++) { const m = r.merges[i]; if (m.t >= this.popCursor && m.t < s) pops.push([this.mxy[i][0], this.mxy[i][1], m.pts]); }
      const key = JSON.stringify([view.header, view.rows]);
      const first = this.lastKey === null, phChange = ph !== this.phSent;
      this.popCursor = Math.max(this.popCursor, s);
      this.sPrev = s;
      if (first || key !== this.lastKey || al.length || phChange || pops.length) {
        const msg = { k: 'b', s, P, header: view.header, rows: view.rows, al, pops, ph };
        if (ph === 'fin' && this.tally === null) { this.tally = r.tally; msg.tally = r.tally; }
        this.lastKey = key; this.phSent = ph;
        this.published.push([s, P, R]);
        this.io.emit(msg);
        const t0 = this.dueAt.get(s); if (t0 !== undefined) this.holdMs.push(this.io.now() - t0);
      }
      if (fin && s === this.tClose()) this.finish();
    }

    // ---- t_Close: the full board, the result, the log (simulate() lines 175-193)
    finish() {
      const r = this.r, RV = this.RV, E = this.E, cfg = this.cfg, brd = this.final, fin = this.fin, tr = this.finalTrace;
      tr.looks = this.looks;
      const ev = RV.evaluate(cfg, brd, tr, fin, r.place, r);
      const boardPlace = RV.boardPlace(brd, fin.Sfinal);
      if (boardPlace !== ev.shown) this.fail('board place ' + boardPlace + ' differs from the shown place ' + ev.shown);
      const Spay = r.bonus && this.nb ? this.nb.S : fin.Sfinal;
      const pp = E.payFor(this.base.rating, Spay, ev.shown);
      let noBonusShown = -1, payNB = -1;
      if (r.bonus && this.nb) {
        const nb = this.nb, fin2 = nb.fin2;
        const tr2 = { Pt: nb.Pt, Ht: tr.Ht, TB: nb.TB, dropTicks: nb.dropTicks, tMark: r.markT, looks: this.looks.filter(l => l.n < 18 && l.t <= fin2.lastDropT).concat([{ t: fin2.overflow ? fin2.tEnd : fin2.lastDropT, n: 18, S: fin2.Sfinal, final: true }]) };
        const brd2 = RV.runBoard(this.mkPar(), this.streamsOf(), tr2, null, fin2);
        noBonusShown = RV.boardPlace(brd2, fin2.Sfinal);
        payNB = E.payFor(this.base.rating, Spay, noBonusShown).pay;
      }
      const recs = RV.records(brd, fin.Sfinal);
      const rows = recs.map(x => ({ handle: x.handle, score: x.score, place: x.place, you: false })).concat([{ handle: this.cfg.copy.boardView.you, score: fin.Sfinal, place: boardPlace, you: true }]).sort((a, b) => a.place - b.place);
      const rung = E.PLACE_RUNG[ev.shown];
      this.finalMsg = { k: 'final', header: cfg.copy.boardView.finalHeader, rows, place: ev.shown, rung, pay: +pp.pay.toFixed(6), S: fin.Sfinal };
      // the round log (released only on a test-API request, after final)
      const L = r.result();
      L.boardHash = boardHash(this.env, brd, fin, this.looks); L.bonusEval = this.bonusEval; L.shown = ev.shown; L.paid = ev.shown; L.boardPlace = boardPlace; L.noBonusShown = noBonusShown; L.payNB = payNB; L.Spay = Spay; L.p = pp.p; L.pay = pp.pay;
      L.looks = this.looks.map(l => [l.t, l.n, l.S, l.final ? 1 : 0]); L.rivals = brd.riv.map(v => ({ handle: v.handle, score: v.R })); L.forcedPlace = this.base.forcedPlace; L.Splay = r.splay; L.tally = r.tally; L.Sfinal = fin.Sfinal;
      L.published = this.published; L.alerts = this.alertLog; L.markT = r.markT; L.dropTicks = r.dropTicks.slice(); L.bankHash = this.env.hashes.bank; L.kernHash = this.env.hashes.kern; L.tEnd = fin.tEnd; L.overflow = fin.overflow; L.tClose = brd.tClose;
      L.firedAlerts = brd.alerts.filter(a => a.state === 'fired').map(a => [a.t, brd.riv[a.rival].handle]); L.errors = this.errors.slice(); L.holdMs = this.holdMs.slice();
      L.ev = { latePassVis: ev.latePassVis, guardSteps: ev.guardSteps, guardRivals: ev.guardRivals, guardFail: ev.guardFail, minGapAbove: ev.minGapAbove, latePass: ev.latePass, guardNear: ev.guardNear };
      if (this.test) { // every published snapshot must equal the final run's Rt/Pof
        let bad = 0; for (const rc of this.snapRecords) { // the evaluated (P, R) of every record must equal the final run; the overflow-end message carries (t_End, Splay, null) and must satisfy P = Splay
          if (rc.Pev !== brd.Pof(rc.s)) bad++; else for (let i = 0; i < 9; i++) if (rc.Rev[i] !== brd.Rt[i][rc.s]) { bad++; break; }
          if (rc.ovfEnd && (rc.P !== r.splay || rc.R !== null)) bad++;
        }
        L.snapCheck = { n: this.snapRecords.length, bad }; if (bad) this.fail('published snapshots differ from the final run: ' + bad);
      }
      this.log = L;
      this.io.emit(this.finalMsg);
      this.done = true;
    }
  }
  FF.Live = Live;
})(typeof self !== 'undefined' ? self : globalThis);
