/** Load and validate the human-written content files.
 *  Every conjunct id in the model must have rule text, and vice versa: a
 *  question we cannot explain is a question we do not ship (DESIGN.md §14). */

import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import YAML from 'yaml';
import { repoPath } from './paths.js';

export const CONTENT_DIR = repoPath('content', 'paxos');

export interface Rule {
  short: string;
  text: string;
}
export interface Misconception {
  title: string;
  belief: string;
  correct: string;
  whyItMatters: string;
}

const rulesDoc = YAML.parse(readFileSync(join(CONTENT_DIR, 'rules.yaml'), 'utf8')) as {
  status: string;
  rules: Record<string, Rule>;
  effects: Record<string, Rule>;
};
const miscDoc = YAML.parse(readFileSync(join(CONTENT_DIR, 'misconceptions.yaml'), 'utf8')) as {
  status: string;
  misconceptions: Record<string, Misconception>;
  definitions: Record<string, Misconception>;
  theories: Record<string, Misconception>;
};

export const RULES: Record<string, Rule> = { ...rulesDoc.rules, ...rulesDoc.effects };
export const MISCONCEPTIONS: Record<string, Misconception> = {
  ...miscDoc.misconceptions,
  ...miscDoc.definitions,
  ...miscDoc.theories,
};
export const CONTENT_STATUS = rulesDoc.status;

export function ruleFor(id: string): Rule {
  const r = RULES[id];
  if (!r) throw new Error(`no rule text for conjunct "${id}" — add it to content/paxos/rules.yaml`);
  return r;
}

/** Assert every conjunct id used by the models has rule text. */
export function checkRuleCoverage(ids: string[]): void {
  const missing = ids.filter((id) => !RULES[id]);
  if (missing.length) throw new Error(`rules.yaml is missing: ${missing.join(', ')}`);
}

/** No protocol notation reaches the reader.
 *
 *  The §10.5 checks assert that a justification references only fields the
 *  renderer displays. That is about information being PRESENT, and it passed
 *  happily on a build whose explanations said things like "an acceptor accepts
 *  a ballot-b proposal only if b is at least as high as maxBal[a]". Present is
 *  not the same as readable, and the difference is the whole point of showing
 *  people concrete scenarios instead of formulas.
 */
const BANNED: [RegExp, string][] = [
  [/\bballot-?\s*b\b/i, 'the variable "b" — say "the ballot" or "that ballot"'],
  [/\bvalue\s+v\b/i, 'the variable "v" — say "the value" or name it'],
  [/\bphase[-\s]?[12][ab]\b/i, 'phase numbers like "phase-2a" — describe who does what'],
  [/\b[12][ab]\s+(message|request|response)/i, 'message codes like "2b message"'],
  [/\bmax(Bal|VBal|Val)\b/, 'a TLA+ variable name'],
  [/\bmsgs\b/, 'a TLA+ variable name'],
];

export function checkNoNotation(): void {
  const problems: string[] = [];
  const scan = (where: string, text: string) => {
    for (const [re, why] of BANNED)
      if (re.test(text)) problems.push(`${where}: ${why}\n    "${text.slice(0, 110)}…"`);
  };
  for (const [id, r] of Object.entries(RULES)) {
    scan(`rules.${id}.short`, r.short);
    scan(`rules.${id}.text`, r.text);
  }
  for (const [id, m] of Object.entries(MISCONCEPTIONS)) {
    scan(`misconceptions.${id}.belief`, m.belief);
    scan(`misconceptions.${id}.correct`, m.correct);
    scan(`misconceptions.${id}.whyItMatters`, m.whyItMatters);
    scan(`misconceptions.${id}.title`, m.title);
  }
  if (problems.length)
    throw new Error(
      `Protocol notation leaked into reader-facing text:\n  ${problems.join('\n  ')}`,
    );
}
