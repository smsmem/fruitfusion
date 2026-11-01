'use strict';
// fork.js — math_8 (MATH_SPEC_8 5.4): cycle-preserving deep copy of a Round (World, Matter engine incl. pairs / detector / timing, bodies, records, stream objects).
// Functions are shared by reference (the Matter event handlers are the only closures; Round.fork() re-binds them). `render` objects are shared (never mutated by the physics).
// Common._nextId / _seed are saved and restored by the caller around the copy and the fork run.
// Speed: a generic `c[k] = ...` copy puts the clone in V8 dictionary mode (3x slower physics). Each distinct key signature gets a compiled factory that builds the clone from an object literal
// (same shape as the original), so the forked physics runs at the speed of the real one. The copy is exact: only identity of the objects differs.
const FACT = new Map();
function factory(keys, hasProto) {
  const sig = (hasProto ? 'P|' : 'O|') + keys.join('\u0001');
  let f = FACT.get(sig); if (f) return f;
  const lit = (hasProto ? '__proto__: pr, ' : '') + keys.map((k, i) => JSON.stringify(k) + ': (typeof v[' + JSON.stringify(k) + '] === "object" && v[' + JSON.stringify(k) + '] !== null && ' + (k === 'render' ? 'false' : 'true') + ') ? null : v[' + JSON.stringify(k) + ']').join(', ');
  const fill = keys.filter(k => k !== 'render').map(k => 'if (typeof v[' + JSON.stringify(k) + '] === "object" && v[' + JSON.stringify(k) + '] !== null) c[' + JSON.stringify(k) + '] = dc(v[' + JSON.stringify(k) + '], seen);').join('\n');
  f = new Function('v', 'dc', 'seen', 'pr', 'const c = {' + lit + '};\nseen.set(v, c);\n' + fill + '\nreturn c;');
  FACT.set(sig, f); return f;
}
function dc(v, seen) {
  if (v === null || typeof v !== 'object') return v;
  const hit = seen.get(v); if (hit !== undefined) return hit;
  if (ArrayBuffer.isView(v)) { const c = new v.constructor(v); seen.set(v, c); return c; }
  if (Array.isArray(v)) { const c = v.slice(); seen.set(v, c); for (let i = 0; i < c.length; i++) { const x = c[i]; if (typeof x === 'object' && x !== null) c[i] = dc(x, seen); } return c; }
  if (v instanceof Set) { const c = new Set(); seen.set(v, c); for (const x of v) c.add(dc(x, seen)); return c; }
  if (v instanceof Map) { const c = new Map(); seen.set(v, c); for (const [k, x] of v) c.set(dc(k, seen), dc(x, seen)); return c; }
  const pr = Object.getPrototypeOf(v), keys = Object.keys(v);
  return factory(keys, pr !== Object.prototype)(v, dc, seen, pr);
}
module.exports = { deepClone: v => dc(v, new Map()) };
