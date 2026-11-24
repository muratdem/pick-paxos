/** Canonical serialization and hashing. DESIGN.md §5.1.
 *
 *  States are plain JSON. Sets are arrays and MUST be canonicalized (sorted by
 *  canonical serialization) before hashing or comparison, or the BFS will treat
 *  the same state as several and every set operation downstream will be wrong.
 */

import type { Value } from './types.js';

/** Stable JSON: object keys sorted, arrays left in place.
 *  Use `canonicalKey` on states, which sorts the arrays the model declares as sets. */
export function stableStringify(v: unknown): string {
  if (v === null || typeof v !== 'object') return JSON.stringify(v) ?? 'null';
  if (Array.isArray(v)) return '[' + v.map(stableStringify).join(',') + ']';
  const o = v as Record<string, unknown>;
  const keys = Object.keys(o).sort();
  return '{' + keys.map((k) => JSON.stringify(k) + ':' + stableStringify(o[k])).join(',') + '}';
}

/** Sort an array of values into canonical order. */
export function sortSet<T>(xs: T[]): T[] {
  return [...xs].sort((a, b) => {
    const sa = stableStringify(a);
    const sb = stableStringify(b);
    return sa < sb ? -1 : sa > sb ? 1 : 0;
  });
}

/** Deduplicate an array of values by canonical form. */
export function uniqSet<T>(xs: T[]): T[] {
  const seen = new Set<string>();
  const out: T[] = [];
  for (const x of xs) {
    const k = stableStringify(x);
    if (!seen.has(k)) {
      seen.add(k);
      out.push(x);
    }
  }
  return out;
}

/** FNV-1a 64-bit, as a hex string. Used for renderer-injectivity checks and
 *  for compact state identity in large BFS runs. */
export function hash(s: string): string {
  let h = 0xcbf29ce484222325n;
  const prime = 0x100000001b3n;
  const mask = 0xffffffffffffffffn;
  for (let i = 0; i < s.length; i++) {
    h ^= BigInt(s.charCodeAt(i));
    h = (h * prime) & mask;
  }
  return h.toString(16).padStart(16, '0');
}

export function deepEqual(a: Value, b: Value): boolean {
  return stableStringify(a) === stableStringify(b);
}

/** Number of differing leaf fields between two canonical JSON values.
 *  Used for contrast distance (DESIGN.md §6.2 step 4). */
export function leafDistance(a: unknown, b: unknown): number {
  if (stableStringify(a) === stableStringify(b)) return 0;
  if (a === null || b === null || typeof a !== 'object' || typeof b !== 'object') return 1;
  if (Array.isArray(a) !== Array.isArray(b)) return 1;
  if (Array.isArray(a) && Array.isArray(b)) {
    let d = Math.abs(a.length - b.length);
    for (let i = 0; i < Math.min(a.length, b.length); i++) d += leafDistance(a[i], b[i]);
    return d;
  }
  const ao = a as Record<string, unknown>;
  const bo = b as Record<string, unknown>;
  const keys = new Set([...Object.keys(ao), ...Object.keys(bo)]);
  let d = 0;
  for (const k of keys) d += leafDistance(ao[k], bo[k]);
  return d;
}
