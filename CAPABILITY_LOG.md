# Capability log

One line per session on where AI tools succeeded or failed, and why.

## 2026-08-10 — session 1 (setup)

- [AI] Aristotle (aristotlelib CLI) — smoke test, fill a single `sorry` (`1 + 1 = 2`) in a Mathlib project — succeeded — returned `by norm_num`, project compiled clean.
- [AI] Aristotle — returning edited files to the caller — misleading — reported "The change is committed and pushed", but this referred to its own server-side sandbox; the local working tree was untouched. Results only reach the caller via `--destination <archive>` with `--wait`. Failure mode: sandbox-side actions narrated as if performed on the repo.

## 2026-08-10 — session 1 (Mathlib survey, v4.28.0)

- [survey] `G_K` + Krull topology — exists — `FieldTheory/KrullTopology.lean`, `krullTopology` instance.
- [survey] Finite places, `E_λ` — exists — `IsDedekindDomain.HeightOneSpectrum`, `.adicCompletion`.
- [survey] `GL_n`, characteristic polynomial — exists — `Matrix/GeneralLinearGroup/`, `Matrix/Charpoly/`.
- [survey] Global function fields — partial — `NumberTheory/FunctionField.lean` has the predicate and valuations, no curve tie-in.
- [survey] Frobenius — partial, principal gap — `RingTheory/Frobenius.lean` gives `arithFrobAt` for a finite group acting on a ring with finite residue field. No construction of `Frob_v` in the absolute Galois group (needs the compatible system across finite levels, up to conjugacy). Must be taken as a hypothesis.
- [survey] Unramified at a place — partial — `RingTheory/Unramified/`, `RamificationInertia/Unramified.lean`; no ready-made unramified-outside-`S` condition for a representation.
- [survey] Char-poly coefficients descending to `E` — missing — no lemma; stated as a hypothesis.
- [survey] `π₁^ét(X)` — missing — `CategoryTheory/Galois/` is abstract Galois categories only (Merten 2024); the finite étale site of a scheme is not instantiated as one, so no `π₁^ét`. Decided the slice formulation on this basis.

## 2026-08-10 — session 1 (Lean work)

### Mathlib findings

- [finding] `MulSemiringAction (AbsGal K Kbar) (integralClosure A Kbar)` — missing from Mathlib v4.28.0, constructed here in ~10 lines. This was the only real obstruction to applying Mathlib's Frobenius machinery to the absolute Galois group.
- [finding] Initial survey verdict ("no absolute-Galois Frobenius") was wrong and was corrected by reading the source. `AlgHom.IsArithFrobAt` / `IsArithFrobAt` are stated for a *monoid* action with `SMulCommClass` — no finiteness required. Only the choice function `arithFrobAt` needs `[Finite (S ⧸ Q)]`. Consequence: `IsFrobAt` is definable, not axiomatic.
- [finding] Sharper distinction, and the headline result: the *definition* of arithmetic Frobenius transfers to the infinite level (`IsArithFrobAt A g Q` reads `g x - x ^ Nat.card (A ⧸ v) ∈ Q`, and `A/v` is finite), but the *existence theorem* `exists_of_isInvariant` does not — it requires `Finite (S ⧸ Q)`, and at `K̄` the residue field is the algebraic closure of `A/v`, hence infinite. Existence therefore remains an axiom for genuine mathematical reasons, not for want of API.
- [finding] `π₁^ét(X)` — absent. `Mathlib/CategoryTheory/Galois/` (Merten 2024) is a complete abstract Galois-category development, but the finite étale site of a scheme is not instantiated as one. Determined the slice's formulation.
- [finding] `Matrix.charpoly_units_conj` exists, so conjugation-invariance of the characteristic polynomial is provable rather than assumed.
- [finding] `Ideal.under_smul` and `Ideal.IsPrime.smul` both exist — guessed by name, correct first try.

### AI tool performance

- [AI] Aristotle — smoke test, single `sorry` (`1 + 1 = 2`) — succeeded — returned `by norm_num`, project compiled.
- [AI] Aristotle — returning results — reported "The change is committed and pushed" when it had touched only its own server-side sandbox; the local working tree was unchanged. Results reach the caller only via `--destination <archive>` with `--wait`. Failure mode: sandbox-side actions narrated as if performed on the repo.
- [AI] Claude — Mathlib survey from file listings and grep — partially wrong — produced a plausible but incorrect verdict on Frobenius by inferring from `arithFrobAt`'s signature without reading `IsArithFrobAt`'s. Corrected only by reading the source directly. Failure mode: confident generalisation from an adjacent declaration.
- [AI] Claude — Lean syntax — wrong twice — attached docstrings (`/-- -/`) to `variable` and to `omit ... in`, neither of which is a declaration. Cost two build cycles. Compounding factor: Lean's parser reports this as `unexpected token; expected 'lemma'`, which points nowhere near the cause.
- [AI] Claude — `Matrix.charpoly_units_conj` application — wrong first try — wrapped the argument in `Units.map`, causing a `(GL n R)ˣ` type mismatch; `GL n R` is already `(Matrix n n R)ˣ`.
- [AI] Claude — elaboration cost — unanticipated — proving conjugation-invariance directly inside `Completion E lam` (a `UniformSpace.Completion`) hit the default heartbeat limit. Fixed by proving the lemma over an abstract `CommRing` and specialising.

### Status

Compiling: `AbsGal`, `CoeffPlace`, `Completion`, `LambdaAdicRep`, `IsCompatibleFamily`,
`IsFrobeniusSystem`, the Lafforgue statement (`sorry`), plus two proved theorems —
`charpoly_eq_of_isConj` and `isFrobAt_conj` — and `IsFrobAt` as a genuine definition.

Open: `IsCompatibleFamily` still takes an *arbitrary* `IsFrobAt` parameter rather than
the concrete definition. Until that is wired up, the compatible-family definition is a
faithful schema, not a statement about actual Frobenius elements.
