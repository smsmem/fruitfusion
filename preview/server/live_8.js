'use strict';
// live_8.js (PREVIEW, build code, not math): the live driver of the math_8 top-out round, one tick at a time. It follows harness_8.js simulate() and counterfactual():
// the same Round options (eager looks, the rescue check at the mark), the same trace (Pt, Ht, TB, Am), runBoard() on the trace so far for each live snapshot, and the
// final run, evaluate(), the no-rescue counterfactual and payFor() at the block. math_8 is NOT frozen (job 011 pilot FAIL); this file is for the gameplay preview only.
(function (G) {
  const FF = G.FF = G.FF || {};
  const SNAP = 6; // a live board snapshot at least 6 ticks apart; spaced out further when runBoard gets slow late in a long round (timing only)

  class Live {
    constructor(env, opt, io) {
      this.env = env; this.io = io; this.cfg = env.cfg; this.RV = env.RV; this.E = env.E; this.test = !!opt.test;
      const cfg = this.cfg, self = this;
      this.base = { serverSeed: opt.serverSeed, clientSeed: opt.clientSeed, nonce: opt.nonce, forcedPlace: opt.forcedPlace || null, rating: opt.rating, botName: null };
      this.tr = { Pt: [], Ht: [], TB: [], Am: [], dropTicks: null, tMark: null, looks: [] };
      const rescueCheck = round => { // harness_8 simulate(): fixed at the mark, a pure function of the trace up to the mark
        if (round.place > cfg.rescue.kMax || round.markT === null) return false;
        const brd = self.RV.runBoard(self.mkPar(), self.streamsOf(), { Pt: self.tr.Pt, Ht: self.tr.Ht, TB: self.tr.TB, Am: self.tr.Am, dropTicks: round.dropTicks, tMark: round.markT, looks: round.looks }, round.markT, null);
        return !!(brd.markInfo && brd.markInfo.rescue);
      };
      this.r = new this.E.Round(Object.assign({}, this.base, { eagerLooks: true, rescueCheck }));
      this.tr.dropTicks = this.r.dropTicks;
      this.mxy = []; { const r = this.r, hm = r.hooks.merged; r.hooks.merged = (rec, a, b, j, x, y) => { hm(rec, a, b, j, x, y); self.mxy.push([x, y]); }; }
      this.T = 0; this.nextSnap = 0; this.sPrev = -1; this.popCursor = 0; this.lastKey = null; this.done = false; this.busy = 0; this.holdMs = []; this.log = null; this.errors = [];
    }
    mkPar() { return { cfg: this.cfg, bank: this.env.bank, kern: this.env.kern, bot: 'rep', place: this.r.place, rating: this.base.rating }; }
    streamsOf() { const b = this.base, s = this.env.rngm.makeStreams(this.env.sha256, b.serverSeed, b.clientSeed, b.nonce); return { board: s.board, rival: s.rival, alert: s.alert }; }

    tick(x) {
      if (this.done) return;
      const r = this.r, tr = this.tr, frameT = this.T, nm0 = r.merges.length, pl0 = r.pomLog.length, mg = [], pp = [];
      const t = r.t;
      tr.Pt.push(r.splay); tr.Ht.push(r.markT === null ? r.topH() : 0); tr.TB.push(r.tbRest()); tr.Am.push(r.areaMax);
      if (x !== null && x !== undefined && !r.input(x)) this.io.emit({ k: 'rej' });
      r.step();
      for (let i = nm0; i < r.merges.length; i++) { const m = r.merges[i], p = this.mxy[i]; mg.push([m.tier, p[0], p[1], m.chainPos]); }
      for (let i = pl0; i < r.pomLog.length; i++) pp.push(r.pomLog[i].pops.length);
      const fr = r.w.view(true).map(f => [f.uid, f.tier, f.x, f.y, f.angle]);
      this.io.emit({ k: 'f', t: frameT, fr, cur: r.ended ? null : r.current, nxt: r.ended ? null : r.next, can: r.canDrop(), cd: Math.max(0, r.allowedAt - r.t), d: r.drops, ap: r.autoplay.active, mg, pp, ov: r.ovCount > 0, h: +r.topH().toFixed(3) });
      this.T++;
      if (r.ended) { this.io.emit({ k: 'end', t: r.t, reason: 'full' }); this.finish(t); return; }
      if (t >= this.nextSnap) { const c0 = this.io.now(); this.publish(t); const c = this.io.now() - c0; this.nextSnap = t + Math.max(SNAP, Math.ceil(c * 2.5 / (1000 / 60))); }
    }
    pops(s) {
      const r = this.r, out = [];
      for (let i = 0; i < r.merges.length; i++) { const m = r.merges[i]; if (m.t >= this.popCursor && m.t <= s) out.push([this.mxy[i][0], this.mxy[i][1], m.pts]); }
      this.popCursor = s + 1; return out;
    }
    publish(s) {
      const r = this.r, RV = this.RV, B = this.cfg.board, t0 = this.io.now();
      const tr = { Pt: this.tr.Pt, Ht: this.tr.Ht, TB: this.tr.TB, Am: this.tr.Am, dropTicks: r.dropTicks, tMark: r.markT, looks: r.looks.filter(l => l.done && l.t <= s) };
      const brd = RV.runBoard(this.mkPar(), this.streamsOf(), tr, s, null);
      const P = brd.Pof(s);
      const view = RV.boardView({ P, rivals: brd.riv.map(v => ({ i: v.i, handle: v.handle, R: brd.Rt[v.i][s] })) }, B.places);
      const al = brd.alerts.filter(a => a.state === 'fired' && a.t > this.sPrev && a.t <= s).map(a => brd.riv[a.rival].handle);
      const pops = this.pops(s), key = JSON.stringify([view.header, view.rows]);
      this.sPrev = s;
      if (this.lastKey === null || key !== this.lastKey || al.length || pops.length) { this.lastKey = key; this.io.emit({ k: 'b', s, P, header: view.header, rows: view.rows, al, pops, ph: 'play' }); }
      this.holdMs.push(this.io.now() - t0);
    }
    // harness_8 counterfactual(): the same inputs on the regular schedule (no rescue); walk-away autoplay finishes it if the inputs run out
    counterfactual() {
      const E = this.E, Cm = this.env.Matter.Common, sId = Cm._nextId, sSeed = Cm._seed, inputs = this.r.inputs;
      const tr2 = { Pt: [], Ht: [], TB: [], Am: [], dropTicks: null, tMark: null, looks: [] };
      const r2 = new E.Round(Object.assign({}, this.base, { noRescue: true, rescueCheck: null, eagerLooks: true }));
      tr2.dropTicks = r2.dropTicks; let k = 0;
      while (!r2.ended) {
        tr2.Pt.push(r2.splay); tr2.Ht.push(r2.markT === null ? r2.topH() : 0); tr2.TB.push(r2.tbRest()); tr2.Am.push(r2.areaMax);
        while (k < inputs.length && inputs[k].t === r2.t) { r2.input(inputs[k].x); k++; }
        r2.step();
        if (r2.t > 400000) throw new Error('cf runaway');
      }
      Cm._nextId = sId; Cm._seed = sSeed;
      tr2.tMark = r2.markT; tr2.looks = r2.looks;
      return { r2, tr2 };
    }
    finish(tLast) {
      const r = this.r, RV = this.RV, E = this.E, cfg = this.cfg, B = cfg.board;
      r.flushLooks();
      const fin = { Sfinal: r.Sfinal, tEnd: r.t, lastDropT: r.lastDropT === null ? 0 : r.lastDropT };
      const tr = { Pt: this.tr.Pt, Ht: this.tr.Ht, TB: this.tr.TB, Am: this.tr.Am, dropTicks: r.dropTicks, tMark: r.markT, looks: r.looks };
      const par = this.mkPar(), brd = RV.runBoard(par, this.streamsOf(), tr, null, fin);
      const ev = RV.evaluate(cfg, brd, tr, fin, r.place, r);
      const boardPlace = RV.boardPlace(brd, fin.Sfinal);
      // the block frame is the final board: one last live snapshot at t_B (ph fin), with the jar tally
      const s = fin.tEnd;
      const view = RV.boardView({ P: fin.Sfinal, rivals: brd.riv.map(v => ({ i: v.i, handle: v.handle, R: v.R })) }, B.places);
      this.io.emit({ k: 'b', s, P: fin.Sfinal, header: view.header, rows: view.rows, al: [], pops: this.pops(s), ph: 'fin', tally: r.tally });
      let Spay = fin.Sfinal, cf = null;
      if (r.rescue.flag && r.rescue.started) {
        try { const c = this.counterfactual(); const fin2 = { Sfinal: c.r2.Sfinal, tEnd: c.r2.t, lastDropT: c.r2.lastDropT === null ? 0 : c.r2.lastDropT }; Spay = fin2.Sfinal; cf = { drops: c.r2.drops, S: fin2.Sfinal, shown: RV.boardPlace(RV.runBoard(par, this.streamsOf(), c.tr2, null, fin2), fin2.Sfinal) }; }
        catch (e) { this.errors.push(String(e && e.message || e)); }
      }
      const pp = E.payFor(this.base.rating, Spay, ev.shown);
      const recs = RV.records(brd, fin.Sfinal);
      const rows = recs.map(x => ({ handle: x.handle, score: x.score, place: x.place, you: false })).concat([{ handle: cfg.copy.boardView.you, score: fin.Sfinal, place: boardPlace, you: true }]).sort((a, b) => a.place - b.place);
      const fm = { k: 'final', header: cfg.copy.boardView.finalHeader, rows, place: ev.shown, rung: E.PLACE_RUNG[ev.shown], pay: +pp.pay.toFixed(6), S: fin.Sfinal, drops: r.drops, poms: r.pomReleased.length };
      const L = r.result(); L.shown = ev.shown; L.boardPlace = boardPlace; L.Spay = Spay; L.cf = cf; L.pay = pp.pay; L.drawn = r.place; L.rescue = r.rescue; L.tieSnaps = ev.tieSnaps; L.passAfterLast = ev.passAfterLast; L.holdMs = this.holdMs; L.errors = this.errors; L.rivals = brd.riv.map(v => ({ handle: v.handle, score: v.R }));
      this.log = L;
      this.io.emit(fm);
      this.done = true;
    }
  }
  FF.Live = Live;
})(typeof self !== 'undefined' ? self : globalThis);
