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

## 2026-08-11 — session 2

### Lean work

- [finding] `IsArithFrobAt.mul_inv_mem_inertia` and `Ideal.inertia` exist in v4.28.0. Frobenius well-definedness at a fixed prime is therefore provable, and was proved (`toHom_eq_of_isArithFrobAt`).
- [finding] Mathlib's `exists_of_isInvariant` needs `[Finite (S ⧸ Q)]`, so it does not apply at `K̄`. Frobenius existence in the absolute Galois group is a genuine gap — a self-contained candidate for a future contribution.
- [decision] Superseded declarations deleted rather than annotated. The development trajectory lives in git history and in this log; the source file shows one correct chain.

### Independent review

An earlier version was reviewed by a separate AI system with no history of this
project. It found four substantive errors, all of which compiled cleanly:

- [error] `IsFrobeniusSystem.isConj_of` asserted that any two Frobenius elements at a place are conjugate. **False.** Two Frobenius lifts at the same prime differ by an inertia element. Had this structure ever been supplied, everything downstream would have been vacuous. Axiom deleted; the correct inertia-based argument proved instead.
- [error] `charpoly_eq_of_isConj` was presented as establishing that condition (2) is well posed. It does not: the argument needs inertia, not conjugacy.
- [error] The Lafforgue statement was false as written. Counterexample: a rank-one unramified character of the constant-field quotient can have Frobenius eigenvalues outside `E`. Irreducibility, finite-order determinant, and `E`-rationality added.
- [error] Frobenius existence was never assumed. Defining a structure with an `exists_frob` field is not assuming it, so the compatibility condition could hold vacuously. Replaced by `FrobeniusChoice` passed as data.
- [error] Minor: `n : ℕ` admitted `n = 0`; unramifiedness used `∃ Q` where `∀ Q` is wanted; `HeightOneSpectrum A` silently indexes an affine model.

### AI tool performance

- [AI] Claude — Lean/Mathlib mechanics — STRONG. Located the missing `MulSemiringAction`, wrote it correctly, found `Matrix.charpoly_units_conj`, `Ideal.under_smul`, `IsArithFrobAt.conj`, and the inertia lemma. Almost every compile failure was mechanical (arity, docstring placement, `noncomputable`) and fixed in one cycle.
- [AI] Claude — mathematical faithfulness — WEAK, and this is the headline finding. Asserted a false axiom without checking it against the decomposition/inertia exact sequence; stated a main theorem missing essential hypotheses; described a lemma as establishing well-definedness when it did not; and wrote README claims that the code did not support. All four compiled. None was caught by `lake build`, by iteration, or by self-review.
- [AI] Claude — self-assessment — UNRELIABLE. Proposed sanity checks that were real but insufficient (`#print axioms` confirms proofs avoid `sorry`; it says nothing about whether definitions are vacuous or statements are true).
- [AI] independent review — DECISIVE. A model with no investment in the prior choices found in one pass what iteration had not. The practical lesson: for formalisation, an adversarial reader is not optional quality assurance, it is the only check on the step that type-checking cannot see — whether the formal statement means the informal one.
- [AI] Aristotle — see session 1. Sandbox-side actions were narrated as if performed on the caller's repository.
