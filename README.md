# Do You Paxos?

A static web app that teaches and tests single-decree Paxos by showing you pairs of
nearly identical scenarios and asking which one the protocol allows. Your answers are
matched against eleven specific misconceptions about how consensus works.

Scope: single-decree Paxos, three levels. Raft, the protocol-comparison level, traces
and invariants are described in the design doc as later milestones and are not part of
this release.

It is an inverted [PICK](https://www.siddharthaprasad.com/papers/pafk-pick.pdf) workflow
(Prasad, Austen, Fisler, Krishnamurthi, ECOOP 2026). PICK knows the user's intent is
unknown and the candidate formulas are known; here the protocol is known and *you* are
the unknown. See [`do-you-paxos-design.md`](do-you-paxos-design.md) for the full design.

**No answer in this app is hand-written.** Every question comes from a model-checked
state space, and the generated banks are checked four different ways before they ship
(see [Correctness](#correctness)).

---

## Quick start

```bash
npm install
npm run build:banks     # generate the question banks (~15s)
npm run dev             # http://localhost:5173
```

`npm run dev` serves the banks from `packages/web/public/banks/`, which `build:banks`
writes. If the app says it cannot load the banks, you skipped that step.

## Everything you can run

| Command | What it does |
|---|---|
| `npm run measure` | Reachable state counts per config and bound. Run before changing bounds. |
| `npm run build:banks` | Generate the question banks into `banks/` and mirror them to the web app. |
| `npm run harness` | **Layer 5** — simulate learners and print the confusion matrix. |
| `npm run crosscheck` | **Layer 1** — check the TypeScript models against TLA+ with TLC (needs Java 17+). |
| `npm test` | Unit tests, including the derived mutant classification. |
| `npm run typecheck` | Strict TypeScript across all packages. |
| `npx tsx packages/pipeline/src/preview.ts <level> [n]` | Print questions as text for eyeballing. |

## Current numbers

Generated at 3 acceptors, 2 values, ballots `{0,1,2}`, BFS depth ≤ 14 — **74,439
reachable states**.

| Level | Questions | Mix (one/both/neither) | Targets |
|---|---|---|---|
| Phase 1 — promises | 24 | 14/5/5 | P5, P6, P11 |
| Phase 2 — proposing and accepting | 40 | 24/8/8 | P1, P2, P3, P4, P7, P8, P9, P10 |
| Is it already decided? | 34 | 16/18/0 | T1, T2, T3 |

Every targeted misconception is identified in **93–100%** of simulated runs, with
off-diagonal confusion at or below 2% except for the P1/P2 pair noted below. No
constant answering strategy exceeds 37%.

## Correctness

The TLC cross-check is a *replication* check: two implementations of the same semantics
agreeing. It cannot catch an error in the semantics, in question selection, in
rendering, or in diagnosis. So there are five layers, not one.

**Layer 1 — the TypeScript model is the TLA+ spec.** `npm run crosscheck` runs TLC over
`specs/tla/paxos/PaxosFlagged.tla` for all twelve configurations and compares reachable
state counts and agreement verdicts against the JavaScript BFS. All twelve match exactly
at two ballots (3,921 states for correct Paxos). The TLA+ spec is the source of truth: if
they disagree, the TypeScript is wrong.

**Layer 2 — the mutants are wrong in the way claimed.** Each mutant's direction
(adding / restricting / overlapping) and its agreement verdict are *derived* by the test
suite and compared against the declaration in `mutants.ts`, rather than asserted by hand.

**Layer 3 — the bounded answer is the real answer.** The anchored level asks a
reachability-closure question ("could this still be chosen?"), whose answer could easily
be an artifact of how many ballots the model allows. Three guards: situations are drawn
only from states with an entirely unused ballot in reserve; anchoring is checked to be
monotone across every edge of the 185k-state graph, which is a property of Paxos rather
than of the fixpoint that computed it; and a sample is re-derived by forward search with
a *second* spare ballot, which must not change any answer.

**Layer 4 — the question is answerable.** Every scenario carries a machine-generated
justification naming the first failing guard conjunct; the build asserts that those
justifications reference only fields the renderer displays, and that no two scenarios —
in particular the two halves of one question — render identically. The build also
rejects protocol notation in any reader-facing text: no `ballot b`, no `value v`, no
`phase-2a`, no TLA+ variable names. Those checks are about information being present and
legible; whether a person can actually follow the screen is a judgement no assertion
makes for us, and the first build failed it badly.

**Layer 5 — the bank actually diagnoses.** `npm run harness` runs the real selection and
scoring against simulated learners: constant strategies must stay near chance, an honest
learner must come out clean, and a learner holding misconception *i* must be identified
as holding *i* in at least 90% of runs. This is the only check that tells you the game
works, and it is the one that found most of the real bugs.

### Known limitations

- **P1 and P2 cannot be fully separated.** P1 ("the leader proposes its own value")
  allows every step P2 ("any reported value is safe") allows, plus more. Containment
  means evidence for P2 is equally evidence for P1. The harness detects this and the
  results screen reports them as a cluster rather than naming both.
- **Some candidates turn out not to be misconceptions.** "A majority currently holds
  this value" is exactly the anchoring condition on every reachable situation the
  anchored level can show, so the build drops it rather than reporting a correct belief
  as an error. The same machinery collapsed D1 and D4 in the earlier `chosen` level.
  Both follow PICK's equivalence-collapsing step, and neither is a bound artifact.
- **"Whoever has the highest vote wins" and "the first vote locks it in" agree on 165 of
  179 situations.** The bank reserves a floor of the 14 that separate them; without it
  the posterior splits and a learner holding either is told nothing.
- **P2's questions are big.** Separating it needs a quorum reporting two different values
  at two different ballots; the smallest such state carries thirteen messages. This is
  where PICK's requirement that scenarios be "small, self-contained" starts to strain.
- Content text is `status: draft` throughout. See the TODO(Murat) markers.

---

## Deploying to GitHub Pages

The repository is not yet a git repo. From a clean checkout, in order:

### 1. Create the repository

```bash
cd /Users/murat.demirbas/Code/pick-paxos
git init -b main
git add -A
git commit -m "Do You Paxos: engine, Paxos models, banks, web app"
```

Then create an **empty** repo on GitHub (no README, no .gitignore) and push:

```bash
gh repo create pick-paxos --public --source=. --remote=origin --push
```

or, without the `gh` CLI, create it in the web UI and then:

```bash
git remote add origin https://github.com/<you>/pick-paxos.git
git push -u origin main
```

### 2. Turn on Pages with GitHub Actions as the source

In the repository: **Settings → Pages → Build and deployment → Source**, choose
**GitHub Actions**. Do *not* choose "Deploy from a branch" — the workflow uses the
Actions deployment path and will fail against a branch source.

This step cannot be done from the CLI and is the one people forget.

### 3. Let the workflow run

`.github/workflows/deploy.yml` triggers on every push to `main`. It regenerates the
banks from the models rather than trusting the committed copies, runs the learner
harness, and fails the deploy if the banks no longer diagnose. Watch it under the
**Actions** tab.

`DYP_BASE` is set automatically from the repository name, so Vite emits asset paths
under `/<repo>/`. If you rename the repo, nothing needs changing.

### 4. Visit the site

```
https://<you>.github.io/pick-paxos/
```

The first deploy takes a couple of minutes; later ones are faster.

### Troubleshooting

| Symptom | Cause |
|---|---|
| Blank page, 404s on `/assets/…` | Pages source is set to a branch instead of GitHub Actions, or `DYP_BASE` does not match the repo name. |
| "Could not load the question banks" | `banks/` was not committed, or `build:banks` failed in CI. Check the Actions log. |
| Deploy job fails on permissions | The `pages: write` and `id-token: write` permissions in `deploy.yml` were removed. |
| TLC job fails locally | Needs Java 17+. `java -version` to check; the jar downloads itself to `tools/`. |

### Running the production build locally first

Worth doing before you push:

```bash
npm run build
npm run preview -w @dyp/web
```

To rehearse the Pages path exactly:

```bash
DYP_BASE=/pick-paxos/ npm run build -w @dyp/web
```

---

## Layout

```
specs/tla/paxos/     TLA+ reference spec with mutation flags — the source of truth
packages/engine/     BFS, canonicalization, pair construction, Bayes, selection
packages/models/     TypeScript Paxos model (structured guard conjuncts) + 11 mutants
packages/pipeline/   measure, build-banks, harness, crosscheck, preview
packages/web/        Vite + React app
content/paxos/       human-written rule and misconception text (YAML, reviewed in PRs)
banks/paxos/         generated question banks (committed, diffed in PRs)
```

Banks are committed so changes to generated questions appear in pull request diffs. CI
regenerates them and fails if the output differs, which makes deterministic seeded
generation a hard requirement.
