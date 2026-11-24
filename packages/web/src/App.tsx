import { useCallback, useEffect, useMemo, useState } from 'react';
import {
  FIT_FLOOR,
  Rng,
  answerMembership,
  fitOf,
  membershipAnswer,
  recompute,
  recomputeCategorical,
  selectNext,
  selectNextExclusive,
  verdict,
  type Answer,
  type AnswerRecord,
  type Bank,
  type Question,
  type Scenario,
} from '@dyp/engine';
import { StateView, StepDelta, type Msg, type PaxosState } from './paxos-view.js';

const BASE = import.meta.env.BASE_URL;
const MAX_PER_LEVEL = 14;

interface Content {
  status: string;
  misconceptions: Record<
    string,
    { title: string; belief: string; correct: string; whyItMatters: string }
  >;
  rules: Record<string, { short: string; text: string }>;
  members: Record<string, string[]>;
  levels: { id: string; order: number; track: string }[];
}

interface Progress {
  answers: Record<string, AnswerRecord[]>;
  /** Questions asked in PREVIOUS runs, per level, so a retry is fresh. */
  seen: Record<string, string[]>;
  /** Per-browser seed, so two people do not get an identical sequence. */
  seed: number;
}

const newSeed = () => Math.floor(Math.random() * 2 ** 31);
const EMPTY: Progress = { answers: {}, seen: {}, seed: 0 };
const KEY = 'dyp:v3:progress';

function load(): Progress {
  try {
    const raw = localStorage.getItem(KEY);
    const p = raw ? { ...EMPTY, ...(JSON.parse(raw) as Progress) } : { ...EMPTY };
    if (!p.seed) p.seed = newSeed();
    return p;
  } catch {
    return { ...EMPTY, seed: newSeed() };
  }
}
function save(p: Progress) {
  try {
    localStorage.setItem(KEY, JSON.stringify(p));
  } catch {
    /* private mode, quota — progress is a convenience, not a feature */
  }
}

/* ------------------------------------------------------------------ */

const stepPre = (s: Scenario) => (s.payload as unknown as { pre: PaxosState }).pre;
const stepPost = (s: Scenario) => (s.payload as unknown as { post: PaxosState }).post;

/** The framing that was missing. Without it nothing else on the screen means
 *  anything: you cannot judge a step without knowing whether ballot 2 is a
 *  second decision or a retry of the first. */
function Setup({ open }: { open: boolean }) {
  return (
    <details className="setup" open={open}>
      <summary>What am I looking at?</summary>
      <div className="setup-body">
        <p>
          <strong>Three acceptors are trying to agree on exactly one thing.</strong> The two
          candidates are <span className="value">Alice</span> and <span className="value">Bob</span>{' '}
          — think of it as choosing who holds a lock, or which of two commands runs first. Only one
          can ever be chosen, and once it is, the decision can never be taken back.
        </p>
        <p>
          This is <strong>single-decree Paxos</strong>: the whole protocol decides that one value
          and then it is done. A <strong>ballot</strong> is one <em>attempt</em> to get that single
          decision made. Ballot 2 is not a second decision — it is a retry of the same one, by a
          proposer who may not know what earlier ballots did. Higher ballot numbers take priority.
        </p>
        <p>
          Each ballot has its own <strong>proposer</strong>, which is a separate thing from the
          acceptors. Proposers do the asking; acceptors do the promising and the accepting. A proposer
          needs a <strong>majority</strong> — any two of the three acceptors — to get anywhere.
        </p>
        <h4>The four things that can happen</h4>
        <ol className="setup-actions">
          <li>
            <strong>A proposer asks for promises.</strong> It picks a ballot number and asks every
            acceptor to promise that ballot.
          </li>
          <li>
            <strong>An acceptor promises.</strong> It agrees to ignore anything older from now on,
            and reports what it last accepted — which is how a decision that was already made gets
            discovered by someone who missed it.
          </li>
          <li>
            <strong>A proposer proposes a value.</strong> Only after a majority has promised. And if
            any of them reported something it had already accepted, the proposer is not free to pick.
          </li>
          <li>
            <strong>An acceptor accepts.</strong> It accepts the value that was proposed.
          </li>
        </ol>
        <p className="setup-chosen">
          A value is <strong>chosen</strong> when a majority of acceptors have all accepted it{' '}
          <em>in the same ballot</em>. Votes spread across different ballots do not add up to a
          decision.
        </p>
      </div>
    </details>
  );
}

function ScenarioCard({
  scenario,
  label,
  kind,
  picked,
  revealed,
}: {
  scenario: Scenario;
  label: 'A' | 'B';
  kind: Question['kind'];
  picked: boolean;
  revealed: boolean;
}) {
  const p = scenario.payload as unknown as Record<string, unknown>;
  const legal = scenario.justification.verdict === 'legal';

  /* Deliberately not clickable. There are four possible answers and a card is
   * only half of one; letting a click stand for "only this one" silently
   * commits an answer the reader did not choose. Answering happens below. */
  return (
    <div
      className={[
        'card',
        picked ? 'card-picked' : '',
        revealed ? (legal ? 'card-legal' : 'card-illegal') : '',
      ]
        .filter(Boolean)
        .join(' ')}
    >
      <div className="card-head">
        <span className="card-label">{label}</span>
        {kind === 'future' ? (
          <span className="card-q">
            Could <strong className="value">{String(p.subject)}</strong> still end up being chosen?
          </span>
        ) : kind === 'chosen' ? (
          <span className="card-q">
            Has <strong className="value">{String(p.subject)}</strong> been chosen?
          </span>
        ) : (
          <span className="card-q">{String(p.describe)}</span>
        )}
        {revealed && (
          <span className={'verdict ' + (legal ? 'yes' : 'no')}>
            {kind === 'future'
              ? legal
                ? 'still possible'
                : 'no longer possible'
              : kind === 'chosen'
                ? legal
                  ? 'yes, chosen'
                  : 'no, not chosen'
                : legal
                  ? 'Paxos allows this'
                  : 'Paxos forbids this'}
          </span>
        )}
      </div>

      {kind === 'step' && (
        <StepDelta pre={stepPre(scenario)} post={stepPost(scenario)} reads={p.reads as Msg[]} />
      )}

      {revealed && <p className="why">{scenario.justification.text}</p>}
    </div>
  );
}

const ANSWERS: { key: Answer; label: string; hint: string }[] = [
  { key: 'A', label: 'Only A', hint: 'a' },
  { key: 'B', label: 'Only B', hint: 'b' },
  { key: 'both', label: 'Both', hint: 'o' },
  { key: 'neither', label: 'Neither', hint: 'n' },
  { key: 'unsure', label: 'Not sure', hint: 'u' },
];

function QuestionView({
  bank,
  question,
  n,
  onAnswer,
}: {
  bank: Bank;
  question: Question;
  n: number;
  onAnswer: (a: Answer) => void;
}) {
  const [given, setGiven] = useState<Answer | null>(null);
  useEffect(() => setGiven(null), [question.id]);

  const revealed = given !== null && given !== 'unsure';
  const truth = membershipAnswer(question.answer['C'] as [boolean, boolean]);

  const commit = useCallback(
    (a: Answer) => {
      if (given !== null) return;
      setGiven(a);
      if (a === 'unsure') onAnswer(a);
    },
    [given, onAnswer],
  );

  useEffect(() => {
    const h = (e: KeyboardEvent) => {
      if (e.metaKey || e.ctrlKey || e.altKey) return;
      const hit = ANSWERS.find((x) => x.hint === e.key.toLowerCase());
      if (hit && given === null) {
        e.preventDefault();
        commit(hit.key);
      } else if (e.key === 'Enter' && revealed) {
        e.preventDefault();
        onAnswer(given!);
      }
    };
    window.addEventListener('keydown', h);
    return () => window.removeEventListener('keydown', h);
  }, [commit, revealed, given, onAnswer]);

  const shown =
    question.kind === 'step'
      ? stepPre(question.a)
      : (question.a.payload as unknown as { state: PaxosState }).state;
  const reads = [
    ...((question.a.payload as unknown as { reads?: Msg[] }).reads ?? []),
    ...((question.b!.payload as unknown as { reads?: Msg[] }).reads ?? []),
  ];

  return (
    <div className="question">
      <div className="qbar">
        <span>
          Question {n} of {MAX_PER_LEVEL}
        </span>
        <span className="qbar-level">{bank.title}</span>
      </div>

      <Setup open={n === 1} />

      <section className="shared">
        <h3>The situation — the same for both options below</h3>
        <StateView state={shown} highlight={reads} />
      </section>

      <p className="prompt">
        {question.kind === 'future'
          ? 'Nothing has been chosen here yet. Which of these could still end up being chosen?'
          : question.kind === 'chosen'
            ? 'Which of these has been chosen? It may be one, both, or neither.'
            : 'Which of these steps does Paxos allow? It may be one, both, or neither.'}
        {question.contrast === 'effect' && (
          <span className="hint">
            Both options are the <strong>same action</strong> by the same acceptor — they differ
            only in what it does. Look at what each one records and announces.
          </span>
        )}
      </p>

      <div className="cards">
        <ScenarioCard
          scenario={question.a}
          label="A"
          kind={question.kind}
          picked={given === 'A' || given === 'both'}
          revealed={revealed}
        />
        <ScenarioCard
          scenario={question.b!}
          label="B"
          kind={question.kind}
          picked={given === 'B' || given === 'both'}
          revealed={revealed}
        />
      </div>

      <div className="answers">
        <span className="answers-label">Your answer</span>
        {ANSWERS.map((a) => (
          <button
            key={a.key}
            className={'ans' + (given === a.key ? ' ans-given' : '')}
            disabled={given !== null}
            onClick={() => commit(a.key)}
          >
            {a.label} <kbd>{a.hint}</kbd>
          </button>
        ))}
      </div>

      {revealed && (
        <div className={'feedback ' + (given === truth ? 'right' : 'wrong')}>
          <strong>
            {given === truth
              ? 'Correct.'
              : `Not quite — the answer is "${ANSWERS.find((x) => x.key === truth)!.label}".`}
          </strong>
          <button className="next" onClick={() => onAnswer(given!)}>
            Next question <kbd>⏎</kbd>
          </button>
        </div>
      )}
    </div>
  );
}

/* ------------------------------------------------------------------ */

function Results({
  bank,
  content,
  answers,
  onRestart,
  onHome,
}: {
  bank: Bank;
  content: Content;
  answers: AnswerRecord[];
  onRestart: () => void;
  onHome: () => void;
}) {
  const misconceptions = bank.configs.filter((c) => c !== 'C');
  const p = bank.exclusive
    ? recomputeCategorical(bank.questions, answers, bank.configs)
    : recompute(bank.questions, answers, misconceptions);

  const byId = new Map(bank.questions.map((q) => [q.id, q]));
  let right = 0;
  let scored = 0;
  for (const a of answers) {
    const q = byId.get(a.questionId);
    if (!q || a.answer === 'unsure') continue;
    scored++;
    if (a.answer === membershipAnswer(q.answer['C'] as [boolean, boolean])) right++;
  }

  /* A misconception is named only if the posterior is high AND the answers are
   * actually coherent with it. Without the second test, random answering
   * reliably produces a confident diagnosis. */
  const likely = misconceptions.filter(
    (m) => verdict(p[m]) === 'likely' && fitOf(bank.questions, answers, m) >= FIT_FLOOR,
  );

  const receiptFor = (m: string) => {
    let best: { q: Question; a: AnswerRecord } | null = null;
    let bestGap = -1;
    for (const a of answers) {
      const q = byId.get(a.questionId);
      if (!q || a.answer === 'unsure' || !q.misconceptions.includes(m)) continue;
      const obs = answerMembership(a.answer)!;
      const mi = q.answer[m] as [boolean, boolean];
      const mc = q.answer['C'] as [boolean, boolean];
      const agreeM = (obs[0] === mi[0] ? 1 : 0) + (obs[1] === mi[1] ? 1 : 0);
      const agreeC = (obs[0] === mc[0] ? 1 : 0) + (obs[1] === mc[1] ? 1 : 0);
      if (agreeM - agreeC > bestGap) {
        bestGap = agreeM - agreeC;
        best = { q, a };
      }
    }
    return best;
  };

  const names = (id: string) =>
    (content.members[id] ?? [id]).map((x) => content.misconceptions[x]?.title ?? x).join(' / ');

  return (
    <div className="results">
      <h2>{bank.title} — results</h2>
      <p className="score">
        You got <strong>{right}</strong> right and <strong>{scored - right}</strong> wrong, out of{' '}
        {scored} answered.
      </p>

      {likely.length === 0 ? (
        /* Three different outcomes land here and they are not the same news.
         * An earlier version collapsed the last two and told someone who got
         * 9 of 14 right that they had maybe been guessing, which is both wrong
         * and rude: no pattern in the misses is the GOOD way to get things
         * wrong. It means scattered slips rather than a rule held incorrectly. */
        right >= Math.ceil(scored * 0.75) ? (
          <div className="panel clean">
            <h3>Nothing to flag.</h3>
            <p>
              Your answers match the protocol on every rule this level tests. That is a result the
              level is built to be able to give, not a default it falls back to.
            </p>
          </div>
        ) : right >= Math.ceil(scored * 0.45) ? (
          <div className="panel clean">
            <h3>Nothing systematic.</h3>
            <p>
              You got {right} of {scored} right, and the {scored - right} you missed do not line up
              with any of the misunderstandings this level looks for. Scattered slips rather than a
              rule held wrongly — which is the good way to get things wrong.
            </p>
            <p>
              The explanation under each question stays on screen after you answer, so the misses
              are worth a second look on the way past.
            </p>
          </div>
        ) : (
          <div className="panel unclear">
            <h3>No clear pattern.</h3>
            <p>
              You got {right} of {scored} right, and the misses do not match any single
              misunderstanding this level knows how to recognise.
            </p>
            <p>
              That can mean the questions were not landing, in which case the explanation under
              each one is the thing to read. Or it can mean you are working from something that is
              not in our list, which is more interesting and which we would like to hear about.
            </p>
          </div>
        )
      ) : (
        likely.map((m) => {
          const info = content.misconceptions[content.members[m]?.[0] ?? m];
          const r = receiptFor(m);
          return (
            <div className="panel likely" key={m}>
              <h3>{names(m)}</h3>
              {content.members[m] && content.members[m].length > 1 && (
                <p className="note">
                  These cannot be told apart on any reachable Paxos state, so they are reported
                  together.
                </p>
              )}
              {info && (
                <>
                  <p>
                    <em>What you appear to believe:</em> {info.belief}
                  </p>
                  <p>
                    <em>What Paxos actually does:</em> {info.correct}
                  </p>
                  <p>
                    <em>Why it matters:</em> {info.whyItMatters}
                  </p>
                </>
              )}
              {r && (
                <p className="receipt">
                  Clearest example: you answered{' '}
                  <strong>{ANSWERS.find((x) => x.key === r.a.answer)?.label}</strong> where Paxos
                  says{' '}
                  <strong>
                    {
                      ANSWERS.find(
                        (x) => x.key === membershipAnswer(r.q.answer['C'] as [boolean, boolean]),
                      )?.label
                    }
                  </strong>
                  .
                </p>
              )}
            </div>
          );
        })
      )}

      <div className="row">
        <button onClick={onRestart}>Try again with different questions</button>
        <button className="ghost" onClick={onHome}>
          Back to the menu
        </button>
      </div>
    </div>
  );
}

/* ------------------------------------------------------------------ */

export default function App() {
  const [progress, setProgress] = useState<Progress>(load);
  const [content, setContent] = useState<Content | null>(null);
  const [banks, setBanks] = useState<Record<string, Bank>>({});
  const [active, setActive] = useState<string | null>(null);
  const [err, setErr] = useState<string | null>(null);

  useEffect(() => {
    (async () => {
      try {
        const c = (await (await fetch(`${BASE}banks/content.json`)).json()) as Content;
        setContent(c);
        const bs: Record<string, Bank> = {};
        for (const l of c.levels)
          bs[l.id] = (await (await fetch(`${BASE}banks/${l.id}.json`)).json()) as Bank;
        setBanks(bs);
      } catch (e) {
        setErr(String(e));
      }
    })();
  }, []);

  const update = useCallback((f: (p: Progress) => Progress) => {
    setProgress((prev) => {
      const next = f(prev);
      save(next);
      return next;
    });
  }, []);

  /* Hash routing (DESIGN.md §11): #level=paxos-chosen */
  useEffect(() => {
    const h = new URLSearchParams(window.location.hash.replace(/^#/, ''));
    const l = h.get('level');
    if (l) setActive(l);
  }, []);

  const bank = active ? banks[active] : null;
  const history = active ? (progress.answers[active] ?? []) : [];

  const current = useMemo(() => {
    if (!bank) return null;
    const asked = new Set(history.map((h) => h.questionId));
    if (asked.size >= MAX_PER_LEVEL) return null;
    const misconceptions = bank.configs.filter((c) => c !== 'C');
    const p = bank.exclusive
      ? recomputeCategorical(bank.questions, history, bank.configs)
      : recompute(bank.questions, history, misconceptions);

    /* Seeded from (browser, level, how far in) so the choice is stable across
     * re-renders but differs between people and between runs. */
    let h = progress.seed >>> 0;
    for (const ch of `${active}:${asked.size}`) h = (Math.imul(h, 31) + ch.charCodeAt(0)) >>> 0;
    const variation = { rng: new Rng(h), seen: new Set(progress.seen[active!] ?? []) };

    if (bank.exclusive) {
      /* Stop late, not early. `fitOf` is the check that keeps a guesser from
       * being handed a confident diagnosis, and over eight answers it is too
       * noisy to tell a guesser from a believer. */
      if (asked.size >= 12 && Math.max(...bank.configs.map((c) => p[c] ?? 0)) > 0.97) return null;
      return selectNextExclusive(bank.questions, asked, p, bank.configs, variation);
    }
    if (asked.size >= 8 && misconceptions.every((m) => p[m] < 0.05 || p[m] > 0.95)) return null;
    return selectNext(bank.questions, asked, p, variation);
  }, [bank, history, progress.seed, progress.seen, active]);

  if (err)
    return (
      <main className="shell">
        <h1>Do You Paxos?</h1>
        <p className="error">Could not load the question banks: {err}</p>
        <p>
          Run <code>npm run build:banks</code> first.
        </p>
      </main>
    );
  if (!content || Object.keys(banks).length === 0)
    return (
      <main className="shell">
        <h1>Do You Paxos?</h1>
        <p>Loading…</p>
      </main>
    );

  /* ---- menu ---- */
  if (!active) {
    const levels = content.levels.slice().sort((a, b) => a.order - b.order);
    return (
      <main className="shell">
        <header className="top">
          <h1>Do You Paxos?</h1>
          <button className="ghost small" onClick={() => update(() => ({ ...EMPTY, seed: newSeed() }))}>
            Reset progress
          </button>
        </header>
        <p className="lede">
          You are shown two nearly identical things that could happen in a Paxos run, and asked
          which of them the protocol actually permits. Every answer is explained straight away. The
          scenarios come from a model-checked state space and are picked to sit exactly where common
          misunderstandings go wrong, so what you get wrong says something specific.
        </p>

        <ol className="levels">
          {levels.map((l) => {
            const b = banks[l.id];
            const done = (progress.answers[l.id] ?? []).length;
            return (
              <li key={l.id}>
                <button className="level" onClick={() => setActive(l.id)}>
                  <strong>{b.title}</strong>
                  <span>{b.blurb}</span>
                  <span className="meta">
                    {done >= MAX_PER_LEVEL
                      ? 'finished — results available'
                      : done > 0
                        ? `in progress — ${done} of ${MAX_PER_LEVEL} answered`
                        : `${MAX_PER_LEVEL} questions, drawn from ${b.questions.length}`}
                  </span>
                </button>
              </li>
            );
          })}
        </ol>

        <p className="foot">
          {content.status === 'draft' && 'The explanation text is still a first draft. '}
          No account and no tracking — your progress is kept in this browser only.
        </p>
      </main>
    );
  }

  /* ---- playing ---- */
  return (
    <main className="shell wide">
      <header className="top">
        <button className="ghost small" onClick={() => setActive(null)}>
          ← Menu
        </button>
      </header>
      {current ? (
        <QuestionView
          bank={bank!}
          question={current}
          n={history.length + 1}
          onAnswer={(a) =>
            update((p) => ({
              ...p,
              answers: {
                ...p.answers,
                [active]: [...(p.answers[active] ?? []), { questionId: current.id, answer: a }],
              },
            }))
          }
        />
      ) : (
        <Results
          bank={bank!}
          content={content}
          answers={history}
          onRestart={() =>
            update((p) => ({
              ...p,
              // Remember what was asked so the next run draws different questions.
              seen: {
                ...p.seen,
                [active]: [
                  ...new Set([
                    ...(p.seen[active] ?? []),
                    ...(p.answers[active] ?? []).map((a) => a.questionId),
                  ]),
                ],
              },
              answers: { ...p.answers, [active]: [] },
            }))
          }
          onHome={() => setActive(null)}
        />
      )}
    </main>
  );
}
