/** Paxos renderers. DESIGN.md §8.
 *
 *  Rule of this file: no protocol notation reaches the screen. No `b=1`, no
 *  `v=x`, no bare "1a / 1b / 2a / 2b". Every message is a full English
 *  sentence naming who did what, and the history is grouped BY BALLOT rather
 *  than by message type, so it reads as the story of each attempt instead of
 *  four unordered buckets.
 *
 *  The build already asserts that the renderer displays every field a
 *  justification depends on (§10.5). That check is about information being
 *  present; it says nothing about whether a person can read it, which is a
 *  judgement no assertion makes for us.
 */

import type { JSX } from 'react';

export interface Msg {
  t: '1a' | '1b' | '2a' | '2b';
  bal: number;
  acc?: number;
  val?: string | null;
  mbal?: number;
  mval?: string | null;
}

export interface PaxosState {
  maxBal: number[];
  maxVBal: number[];
  maxVal: (string | null)[];
  msgs: Msg[];
}

export const accName = (i: number) => `Acceptor ${i + 1}`;

export const msgKey = (m: Msg) =>
  `${m.t}|${m.bal}|${m.acc ?? ''}|${m.val ?? ''}|${m.mbal ?? ''}|${m.mval ?? ''}`;

/** The phase a message belongs to, in protocol order within a ballot. */
const PHASE: Record<Msg['t'], number> = { '1a': 0, '1b': 1, '2a': 2, '2b': 3 };

/** One message as a sentence. */
export function msgSentence(m: Msg): JSX.Element {
  switch (m.t) {
    case '1a':
      return (
        <>
          The <strong>proposer</strong> asks every acceptor to promise this ballot.
        </>
      );
    case '1b':
      return (
        <>
          <strong>{accName(m.acc!)}</strong> promises this ballot
          {m.mbal! < 0 ? (
            <>, and reports that it has not accepted anything.</>
          ) : (
            <>
              , and reports what it last accepted: <strong className="value">{m.mval}</strong> in ballot{' '}
              {m.mbal}.
            </>
          )}
        </>
      );
    case '2a':
      return (
        <>
          The <strong>proposer</strong> proposes <strong className="value">{m.val}</strong>.
        </>
      );
    case '2b':
      return (
        <>
          <strong>{accName(m.acc!)}</strong> accepts <strong className="value">{m.val}</strong>.
        </>
      );
  }
}

/** Standalone version, for cards where the ballot is not implied by a heading. */
export function msgSentenceFull(m: Msg): JSX.Element {
  return (
    <>
      {msgSentence(m)} <span className="in-ballot">(ballot {m.bal})</span>
    </>
  );
}

/* ------------------------------------------------------------------ */

/** Where each acceptor stands right now, in words. */
export function AcceptorStanding({
  state,
  prev,
}: {
  state: PaxosState;
  prev?: PaxosState;
}): JSX.Element {
  return (
    <div className="standing">
      {state.maxBal.map((_, i) => {
        const changed =
          prev &&
          (prev.maxBal[i] !== state.maxBal[i] ||
            prev.maxVBal[i] !== state.maxVBal[i] ||
            prev.maxVal[i] !== state.maxVal[i]);
        return (
          <div className={'standing-row' + (changed ? ' changed' : '')} key={i}>
            <span className="who">{accName(i)}</span>
            <span className="facts">
              {state.maxBal[i] < 0 ? (
                <>has promised nothing yet</>
              ) : (
                <>
                  has promised <strong>ballot {state.maxBal[i]}</strong>
                </>
              )}
              {' · '}
              {state.maxVBal[i] < 0 ? (
                <>has not accepted anything</>
              ) : (
                <>
                  last accepted <strong className="value">{state.maxVal[i]}</strong> in ballot{' '}
                  {state.maxVBal[i]}
                </>
              )}
            </span>
          </div>
        );
      })}
    </div>
  );
}

/** What has happened, ballot by ballot. Each ballot is one attempt to get the
 *  single decision made, so this is the natural narrative unit. */
export function History({
  state,
  highlight,
}: {
  state: PaxosState;
  highlight?: Msg[];
}): JSX.Element {
  const hi = new Set((highlight ?? []).map(msgKey));
  if (state.msgs.length === 0)
    return <p className="empty">Nothing has happened yet — no ballot has been started.</p>;

  const ballots = [...new Set(state.msgs.map((m) => m.bal))].sort((a, b) => a - b);

  return (
    <div className="history">
      {ballots.map((b) => {
        const ms = state.msgs
          .filter((m) => m.bal === b)
          .sort((x, y) => PHASE[x.t] - PHASE[y.t] || (x.acc ?? 0) - (y.acc ?? 0));
        return (
          <div className="ballot" key={b}>
            <div className="ballot-name">Ballot {b}</div>
            <ol className="ballot-steps">
              {ms.map((m) => (
                <li className={hi.has(msgKey(m)) ? 'read' : ''} key={msgKey(m)}>
                  {msgSentence(m)}
                </li>
              ))}
            </ol>
          </div>
        );
      })}
    </div>
  );
}

export function StateView({
  state,
  prev,
  highlight,
}: {
  state: PaxosState;
  prev?: PaxosState;
  highlight?: Msg[];
}): JSX.Element {
  return (
    <div className="state-view">
      <div className="section">
        <h4>Where each acceptor stands</h4>
        <AcceptorStanding state={state} prev={prev} />
      </div>
      <div className="section">
        <h4>What has happened so far</h4>
        <History state={state} highlight={highlight} />
      </div>
    </div>
  );
}

/* ------------------------------------------------------------------ */

/** What a step does, in causal order: what it looks at, then what it changes,
 *  then what it announces. Reads come first because the whole question is
 *  whether what it looked at justifies what it did. */
export function StepDelta({
  pre,
  post,
  reads,
}: {
  pre: PaxosState;
  post: PaxosState;
  reads?: Msg[];
}): JSX.Element {
  const before = new Set(pre.msgs.map(msgKey));
  const sent = post.msgs.filter((m) => !before.has(msgKey(m)));
  const changed = pre.maxBal
    .map((_, i) => i)
    .filter(
      (i) =>
        pre.maxBal[i] !== post.maxBal[i] ||
        pre.maxVBal[i] !== post.maxVBal[i] ||
        pre.maxVal[i] !== post.maxVal[i],
    );

  return (
    <div className="delta">
      <div className="delta-row">
        <span className="delta-label">Looks at</span>
        <div className="delta-body">
          {!reads || reads.length === 0 ? (
            <span className="delta-none">nothing — this step needs no earlier message</span>
          ) : (
            <ul>
              {reads.map((m) => (
                <li key={msgKey(m)}>{msgSentenceFull(m)}</li>
              ))}
            </ul>
          )}
        </div>
      </div>

      <div className="delta-row">
        <span className="delta-label">Then records</span>
        <div className="delta-body">
          {changed.length === 0 ? (
            <span className="delta-none">nothing — no acceptor changes its mind</span>
          ) : (
            <ul>
              {changed.map((i) => (
                <li key={i}>
                  <strong>{accName(i)}</strong>
                  {pre.maxBal[i] !== post.maxBal[i] && (
                    <span className="change">
                      now promises{' '}
                      {post.maxBal[i] < 0 ? 'nothing' : `ballot ${post.maxBal[i]}`}
                      <span className="was">
                        {' '}
                        (was {pre.maxBal[i] < 0 ? 'nothing' : `ballot ${pre.maxBal[i]}`})
                      </span>
                    </span>
                  )}
                  {(pre.maxVBal[i] !== post.maxVBal[i] || pre.maxVal[i] !== post.maxVal[i]) && (
                    <span className="change">
                      last accepted is now{' '}
                      {post.maxVBal[i] < 0 ? (
                        'none'
                      ) : (
                        <>
                          <strong className="value">{post.maxVal[i]}</strong> in ballot{' '}
                          {post.maxVBal[i]}
                        </>
                      )}
                      <span className="was">
                        {' '}
                        (was{' '}
                        {pre.maxVBal[i] < 0
                          ? 'none'
                          : `${pre.maxVal[i]} in ballot ${pre.maxVBal[i]}`}
                        )
                      </span>
                    </span>
                  )}
                </li>
              ))}
            </ul>
          )}
        </div>
      </div>

      <div className="delta-row">
        <span className="delta-label">And announces</span>
        <div className="delta-body">
          {sent.length === 0 ? (
            <span className="delta-none">nothing new</span>
          ) : (
            <ul>
              {sent.map((m) => (
                <li className="sent" key={msgKey(m)}>
                  {msgSentenceFull(m)}
                </li>
              ))}
            </ul>
          )}
        </div>
      </div>
    </div>
  );
}
