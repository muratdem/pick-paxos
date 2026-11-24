/** Render a sample of bank questions as text for human review. DESIGN.md §10.5.
 *  Usage: npx tsx packages/pipeline/src/preview.ts <level> [count] */

import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import type { Bank, Question, Scenario } from '@dyp/engine';
import { repoPath } from './paths.js';

const level = process.argv[2] ?? 'paxos-phase2-steps';
const count = Number(process.argv[3] ?? 3);
const bank = JSON.parse(
  readFileSync(repoPath('banks', 'paxos', `${level}.json`), 'utf8'),
) as Bank;

interface Msg {
  t: string;
  bal: number;
  acc?: number;
  val?: string | null;
  mbal?: number;
  mval?: string | null;
}
interface St {
  maxBal: number[];
  maxVBal: number[];
  maxVal: (string | null)[];
  msgs: Msg[];
}

const acc = (i: number) => `a${i + 1}`;
const d = (n: number) => (n < 0 ? '-' : String(n));

const msg = (m: Msg) =>
  m.t === '1a'
    ? `1a(b=${m.bal})`
    : m.t === '1b'
      ? `1b(${acc(m.acc!)},b=${m.bal},last=${m.mbal! < 0 ? 'none' : `b${m.mbal}:${m.mval}`})`
      : m.t === '2a'
        ? `2a(b=${m.bal},v=${m.val})`
        : `2b(${acc(m.acc!)},b=${m.bal},v=${m.val})`;

function showState(s: St, indent = '    ') {
  const rows = s.maxBal
    .map((_, i) => `${acc(i)}[promised=${d(s.maxBal[i])} voted=${d(s.maxVBal[i])}:${s.maxVal[i] ?? '-'}]`)
    .join(' ');
  console.log(`${indent}${rows}`);
  console.log(`${indent}msgs: ${s.msgs.map(msg).join(' ') || '(none)'}`);
}

const ANS = (m: [boolean, boolean]) =>
  m[0] && m[1] ? 'Both' : m[0] ? 'A only' : m[1] ? 'B only' : 'Neither';

console.log(`${bank.level} — ${bank.title}`);
console.log(`${bank.questions.length} questions, mix ${bank.mix.one}/${bank.mix.both}/${bank.mix.neither}\n`);

const show = (q: Question) => {
  console.log('─'.repeat(78));
  console.log(`${q.id}   type=${q.type}  distance=${q.distance}  size=${q.size}`);
  console.log(`targets: ${q.misconceptions.join(', ')}`);

  const side = (sc: Scenario, label: string) => {
    const p = sc.payload as unknown as Record<string, unknown>;
    console.log(`\n  [${label}] ${p.describe ?? `has "${p.subject}" been chosen?`}`);
    if (p.action) {
      console.log(`    action: ${p.action}(${JSON.stringify(p.params)})`);
      console.log('    after:');
      showState(p.post as St);
    }
    console.log(`    => ${sc.justification.verdict.toUpperCase()}`);
    console.log(`    ${sc.justification.text.replace(/\s+/g, ' ').slice(0, 300)}`);
  };

  const pre = (q.a.payload as unknown as { pre?: St; state?: St });
  console.log('\n  BEFORE:');
  showState((pre.pre ?? pre.state)!);
  side(q.a, 'A');
  side(q.b!, 'B');
  console.log(`\n  ANSWER (Paxos): ${ANS(q.answer['C'] as [boolean, boolean])}`);
  const others = bank.configs
    .filter((c) => c !== 'C' && q.misconceptions.includes(c))
    .map((c) => `${c}:${ANS(q.answer[c] as [boolean, boolean])}`);
  console.log(`  a learner holding...  ${others.join('   ')}`);
  console.log();
};

for (const q of bank.questions.slice(0, count)) show(q);
