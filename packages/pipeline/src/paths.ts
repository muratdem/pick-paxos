/** Resolve repo-relative paths from the module location, not from cwd.
 *  npm runs workspace scripts with cwd set to the package directory, so
 *  process.cwd() is packages/pipeline, not the repo root. */
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

export const REPO_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..', '..');
export const repoPath = (...parts: string[]) => join(REPO_ROOT, ...parts);
