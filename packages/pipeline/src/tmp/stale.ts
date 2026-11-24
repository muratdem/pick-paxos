import { buildIndex } from '../anchored.js';
import { defaultConstants, paxos, type PaxosState } from '@dyp/models';
const K = defaultConstants([0, 1, 2]);
const m = paxos(K);

const stale = (s: PaxosState) =>
  K.values.some(
    (v) =>
      K.quorums.some((q) => q.every((a) => s.msgs.some((x) => x.t === '2b' && x.acc === a && x.val === v))) &&
      !K.quorums.some((q) => q.every((a) => s.maxVal[a] === v)),
  );
const nothingChosen = (s: PaxosState) => !K.values.some((v) => m.predicates[`C0:${v}`](s));

// rebuild Murat's state
let s: PaxosState = m.init()[0];
const step = (a: string, p: Record<string, unknown>) => {
  const en = m.enabled(s, a, p as never);
  if (!en.ok) throw new Error(`${a} blocked by ${en.failed}`);
  s = m.actions.find((x) => x.name === a)!.effect(s, p as never);
};
step('Phase1a',{bal:0}); step('Phase1b',{acc:0,bal:0}); step('Phase1b',{acc:1,bal:0});
step('Phase2a',{bal:0,val:'Alice',quorum:[0,1]}); step('Phase2b',{acc:0,bal:0,val:'Alice'});
step('Phase1a',{bal:1}); step('Phase1b',{acc:1,bal:1}); step('Phase1b',{acc:2,bal:1});
step('Phase2a',{bal:1,val:'Bob',quorum:[1,2]}); step('Phase2b',{acc:0,bal:1,val:'Bob'});
step('Phase1a',{bal:2}); step('Phase1b',{acc:1,bal:2}); step('Phase1b',{acc:2,bal:2});
step('Phase2a',{bal:2,val:'Alice',quorum:[1,2]}); step('Phase2b',{acc:1,bal:2,val:'Alice'});
console.log('target state: stale =', stale(s), ' nothingChosen =', nothingChosen(s), ' msgs =', s.msgs.length);

for (const d of [15, 16, 17]) {
  const g = buildIndex(m, 500_000, d);
  const has = g.idOf.has(m.key(s));
  let n = 0, nStaleOk = 0;
  for (const st of g.state) if (stale(st)) { n++; if (nothingChosen(st)) nStaleOk++; }
  console.log(`depth<=${d}: ${g.key.length} states; target present=${has}; stale=${n}; stale & nothing chosen=${nStaleOk}`);
}
