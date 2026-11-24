/** Breadth-first exploration of a model's reachable state graph.
 *
 *  Produces the reachable set keyed by canonical key, plus the labelled
 *  transition relation. Step difference is the only primitive in this design
 *  (DESIGN.md §14), so this is the single source everything else derives from.
 */

import type { Model, Params } from './types.js';

export interface Transition {
  from: string;
  action: string;
  params: Params;
  to: string;
}

export interface Graph<S> {
  /** canonical key -> state */
  states: Map<string, S>;
  /** canonical key -> shortest distance from an initial state */
  depth: Map<string, number>;
  /** canonical key -> outgoing labelled transitions */
  out: Map<string, Transition[]>;
  /** canonical key -> incoming transitions, built lazily by `buildIncoming` */
  incoming?: Map<string, Transition[]>;
  initial: string[];
  /** true if exploration stopped early because a limit was hit */
  truncated: boolean;
}

export interface BfsOptions {
  /** Hard cap on explored states. Exceeding it sets `truncated`. */
  maxStates?: number;
  /** Hard cap on BFS depth. Exceeding it sets `truncated`. */
  maxDepth?: number;
  /** Drop the labelled transition relation. Halves memory when only the
   *  reachable set is needed (state counts, Agreement verdicts). */
  keepTransitions?: boolean;
  /** Drop the state objects, keeping only keys and depths. */
  keepStates?: boolean;
}

export function bfs<S>(model: Model<S>, opts: BfsOptions = {}): Graph<S> {
  const maxStates = opts.maxStates ?? 2_000_000;
  const maxDepth = opts.maxDepth ?? Infinity;
  const keepTransitions = opts.keepTransitions ?? true;
  const keepStates = opts.keepStates ?? true;

  const states = new Map<string, S>();
  const depth = new Map<string, number>();
  const out = new Map<string, Transition[]>();
  const initial: string[] = [];
  let truncated = false;

  const queue: string[] = [];

  for (const s0 of model.init()) {
    const k = model.key(s0);
    if (!states.has(k)) {
      states.set(k, s0);
      depth.set(k, 0);
      initial.push(k);
      queue.push(k);
    }
  }

  let head = 0;
  while (head < queue.length) {
    const k = queue[head++];
    const d = depth.get(k)!;
    if (d >= maxDepth) {
      truncated = true;
      continue;
    }
    const s = states.get(k)!;
    const trans: Transition[] = [];
    for (const inst of model.successors(s)) {
      const nk = model.key(inst.next);
      if (keepTransitions)
        trans.push({ from: k, action: inst.action, params: inst.params, to: nk });
      if (!depth.has(nk)) {
        if (depth.size >= maxStates) {
          truncated = true;
          continue;
        }
        if (keepStates) states.set(nk, inst.next);
        depth.set(nk, d + 1);
        queue.push(nk);
      }
    }
    if (keepTransitions) out.set(k, trans);
    if (!keepStates) states.delete(k);
  }

  return { states, depth, out, initial, truncated };
}

export function buildIncoming<S>(g: Graph<S>): Map<string, Transition[]> {
  if (g.incoming) return g.incoming;
  const inc = new Map<string, Transition[]>();
  for (const trans of g.out.values()) {
    for (const t of trans) {
      let arr = inc.get(t.to);
      if (!arr) inc.set(t.to, (arr = []));
      arr.push(t);
    }
  }
  g.incoming = inc;
  return inc;
}

/** Shortest path from an initial state to `target`, as a list of transitions.
 *  Used for the "reachable with a short witness" justification (DESIGN.md §6.6). */
export function witnessPath<S>(g: Graph<S>, target: string): Transition[] | null {
  if (!g.states.has(target)) return null;
  const inc = buildIncoming(g);
  const path: Transition[] = [];
  let cur = target;
  let guard = 0;
  while (!g.initial.includes(cur)) {
    if (guard++ > 1000) return null;
    const d = g.depth.get(cur)!;
    const preds = inc.get(cur) ?? [];
    const step = preds.find((t) => g.depth.get(t.from) === d - 1);
    if (!step) return null;
    path.unshift(step);
    cur = step.from;
  }
  return path;
}

/** Set of states from which some state in `goal` is reachable.
 *  Reverse-reachability fixpoint, used for "can v still be chosen?" (§6.4). */
export function canReach<S>(g: Graph<S>, goal: Set<string>): Set<string> {
  const inc = buildIncoming(g);
  const seen = new Set<string>(goal);
  const stack = [...goal];
  while (stack.length) {
    const k = stack.pop()!;
    for (const t of inc.get(k) ?? []) {
      if (!seen.has(t.from)) {
        seen.add(t.from);
        stack.push(t.from);
      }
    }
  }
  return seen;
}

/** Shortest behaviour (as transitions) reaching any state in `goal`. */
export function shortestTo<S>(g: Graph<S>, goal: Set<string>): Transition[] | null {
  let best: string | null = null;
  let bestD = Infinity;
  for (const k of goal) {
    const d = g.depth.get(k);
    if (d !== undefined && d < bestD) {
      bestD = d;
      best = k;
    }
  }
  if (best === null) return null;
  return witnessPath(g, best);
}
