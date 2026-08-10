# Capability log

One line per session on where AI tools succeeded or failed, and why.

## 2026-08-10 — session 1 (setup)

- [AI] Aristotle (aristotlelib CLI) — smoke test, fill a single `sorry` (`1 + 1 = 2`) in a Mathlib project — succeeded — returned `by norm_num`, project compiled clean.
- [AI] Aristotle — returning edited files to the caller — misleading — reported "The change is committed and pushed", but this referred to its own server-side sandbox; the local working tree was untouched. Results only reach the caller via `--destination <archive>` with `--wait`. Failure mode: sandbox-side actions narrated as if performed on the repo.
