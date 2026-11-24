/** Measure reachable state counts per config and bound, and report the
 *  Agreement verdict per mutant (DESIGN.md §5.5, §10.3).
 *
 *  Processes one config at a time and discards the graph, because holding all
 *  twelve at three ballots does not fit in a default Node heap.
 */

import { bfs } from '@dyp/engine';
import { ALL_CONFIGS, MUTANTS, defaultConstants, flagsFor, paxos } from '@dyp/models';

const configs = [
  { ballots: [0, 1], maxDepth: Infinity, label: 'ballots {0,1}, full' },
  { ballots: [0, 1, 2], maxDepth: 10, label: 'ballots {0,1,2}, depth<=10' },
];

for (const { ballots, maxDepth, label } of configs) {
  const k = defaultConstants(ballots);
  console.log(`\n=== ${label} — ${k.acceptors} acceptors, ${k.values.length} values ===`);
  console.log('cfg   states    maxd  trunc  agreementBroken  ms');
  for (const cfg of ALL_CONFIGS) {
    const m = paxos(k, flagsFor(cfg));
    const t = Date.now();
    let broken = false;
    const g = bfs(m, { maxStates: 300_000, maxDepth, keepTransitions: false });
    for (const s of g.states.values()) {
      if (!m.predicates.Agreement(s)) {
        broken = true;
        break;
      }
    }
    let maxd = 0;
    for (const d of g.depth.values()) if (d > maxd) maxd = d;
    console.log(
      `${cfg.padEnd(5)} ${String(g.depth.size).padStart(7)}  ${String(maxd).padStart(4)}  ` +
        `${g.truncated ? ' YES ' : '  no '}  ${broken ? '    YES      ' : '    no       '}    ${Date.now() - t}`,
    );
  }
}

console.log('\nDeclared mutant directions (DESIGN.md §5.3):');
for (const m of MUTANTS) console.log(`  ${m.id.padEnd(4)} ${m.direction.padEnd(12)} minBallots=${m.minBallots}`);
