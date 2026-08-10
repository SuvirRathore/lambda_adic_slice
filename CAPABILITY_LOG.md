# Capability log

One line per session on where AI tools succeeded or failed, and why.

## 2026-08-10 — session 1 (setup)

- [AI] Aristotle (aristotlelib CLI) — smoke test, fill a single `sorry` (`1 + 1 = 2`) in a Mathlib project — succeeded — returned `by norm_num`, project compiled clean.
- [AI] Aristotle — returning edited files to the caller — misleading — reported "The change is committed and pushed", but this referred to its own server-side sandbox; the local working tree was untouched. Results only reach the caller via `--destination <archive>` with `--wait`. Failure mode: sandbox-side actions narrated as if performed on the repo.

## 2026-08-10 — session 1 (Mathlib survey, v4.28.0)

- [survey] `G_K` + Krull topology — EXISTS — `FieldTheory/KrullTopology.lean`, `krullTopology` instance.
- [survey] Finite places, `E_λ` — EXISTS — `IsDedekindDomain.HeightOneSpectrum`, `.adicCompletion`.
- [survey] `GL_n`, characteristic polynomial — EXISTS — `Matrix/GeneralLinearGroup/`, `Matrix/Charpoly/`.
- [survey] Global function fields — PARTIAL — `NumberTheory/FunctionField.lean` has the predicate and valuations, no curve tie-in.
- [survey] Frobenius — PARTIAL, PRINCIPAL GAP — `RingTheory/Frobenius.lean` gives `arithFrobAt` for a FINITE group acting on a ring with finite residue field. No construction of `Frob_v` in the absolute Galois group (needs the compatible system across finite levels, up to conjugacy). Must be taken as a hypothesis.
- [survey] Unramified at a place — PARTIAL — `RingTheory/Unramified/`, `RamificationInertia/Unramified.lean`; no ready-made unramified-outside-`S` condition for a representation.
- [survey] Char-poly coefficients descending to `E` — MISSING — no lemma; stated as a hypothesis.
- [survey] `π₁^ét(X)` — MISSING — `CategoryTheory/Galois/` is abstract Galois categories only (Merten 2024); the finite étale site of a scheme is not instantiated as one, so no `π₁^ét`. Decided the slice formulation on this basis.
