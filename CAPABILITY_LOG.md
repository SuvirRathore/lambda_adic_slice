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

## 11-08-2026 — second independent review

**Findings.** The main theorem, already repaired once, was still stronger than
Lafforgue's theorem in two independent ways, both filed in the README as
"limitations": the conclusion placed companions over `E_λ` itself, and the
irreducibility hypothesis was irreducibility over `E_λ` rather than absolute
irreducibility — a weaker hypothesis, hence a stronger theorem. `A` was an
arbitrary Dedekind domain with `Frac A = K`, unconnected to `𝔽_q`; for `A` a
DVR or a field, `HeightOneSpectrum A` is a single point or empty and the
conclusion is satisfiable by an everywhere-unramified companion-matrix
construction. A docstring on `charpoly_eq_of_isConj` still asserted the
well-definedness claim the first review had rejected, and still cited
`IsFrobeniusSystem.isConj_of`, an axiom deleted in that same round.

**Failure mode.** The first round's fixes were applied where the reviewer
pointed, not systematically. Code and documentation drifted apart, and the
surviving false claim was in the documentation. `lake build` and `#print axioms`
were both clean throughout.

**Repairs.** `exists_companion` replaces the old theorem, stated pointwise in
`λ`, with the companion over a bundled finite extension `M/E_λ` carrying the
module topology. `A` is now a finite-type `𝔽_q`-algebra with scalar towers to
`K`. `SpanFull` gives absolute irreducibility with no algebraic closure. The
Frobenius polynomials `P` are data, which ties the companion to `ρ₀` and lets
the type-inappropriate clause `ρ_{λ₀} = ρ₀` be dropped.

**Mathlib facts established by reading source, not by guessing.**
- `IsArithFrobAt` is `∀ x, σ • x - x ^ Nat.card (R ⧸ Q.under R) ∈ Q`. If the base
  residue ring is infinite the cardinal is `0` and the congruence at `x = 0`
  forces `Q = ⊤`, contradicting primality (`AlgHom.IsArithFrobAt.finite_quotient`).
  So the definition self-protects against a `q = 0` degeneracy, at the cost of
  making `FrobeniusChoice` uninhabited when a residue field is infinite.
- `IsArithFrobAt.conj` and `IsArithFrobAt.mul_inv_mem_inertia` require no
  finiteness; only `exists_of_isInvariant` does.
- `IsModuleTopology` exists in v4.28.0
  (`Mathlib/Topology/Algebra/Module/ModuleTopology.lean`, Buzzard–Sawin). This is
  what makes the finite-extension coefficient field expressible: the topology on
  `M` is pinned rather than supplied as arbitrary data, so `Continuous` on the
  companion means something.

**Literature check.** Drinfeld, arXiv:1007.4004, §1.1–1.2: Theorem 1.1 produces a
lisse sheaf over an algebraic closure of `E_λ`, and the curve case is Lafforgue's
Theorem VII.6. Deligne's Conjecture 1.3(b) asks for a lisse `E_λ`-sheaf only
after possibly enlarging `E`, and Drinfeld attributes the passage from `Ē_λ` to
`E_λ` to Chin, Adv. Math. 180 (2003) — not to Lafforgue, and not to Chin's later
monodromy-group paper.

**Unchanged.** The W30 candidate remains "Frobenius elements exist in the
absolute Galois group": genuinely missing, self-contained, and a plausible
Mathlib PR.

## 11-08-2026 — third independent review

Run against the repaired state, with the round-1 and round-2 transcripts withheld
to avoid anchoring on the same questions.

**Verdict.** No false content, no vacuity, no code/documentation drift. All five
proved lemmas re-derived and their Mathlib dependencies checked against v4.28.0
source. The `sorry`'d statement judged a faithful, satisfiable, honestly-scoped
rendering of Lafforgue's companion theorem for the affine curve, neither stronger
nor weaker than the literature package. Non-degenerate satisfiability exhibited:
`A = 𝔽_q[t]`, `ρ₀` the 2-dimensional representation of an `S₃`-cover.

**Corrected.** Two prose overclaims. The integrality remark attributed unit-ness
of the Frobenius roots to purity; it is instead part (c) of Deligne's Conjecture
1.2.10, proved for curves by Lafforgue VII.6, and is a conclusion separate from
the weight condition — Drinfeld's own `Γ^mix` versus `Γ^mot` distinction makes
this explicit, and `(3+4i)/5` is a one-line witness that purity does not imply
integrality. The `SpanFull` docstring stated the Burnside equivalence without its
scope: it needs `R` a field and `m ≥ 1`, both of which hold at every use site but
neither of which was said. Three cosmetic gaps also closed.

**A claim of ours that was wrong.** We had reasoned that continuity of a
representation of `G_K` into `GL_n(E_λ)` forces unramifiedness at almost all
places. False for `n ≥ 2`. Compactness gives a stable lattice and hence a finite
ramification set at each finite level, but the level-wise sets need not stabilise:
a Kummer class built from `b_m = ∏_{i≤m} π_i^{ℓ^i}` gives a continuous
upper-triangular `ρ = (χ_ℓ, c; 0, 1) : G_K → GL₂(ℤ_ℓ)` ramified at every `v_i`.
Ramakrishna, *Infinitely ramified Galois representations*, Ann. of Math. 151
(2000), shows even full image is compatible with infinite ramification;
Khare–Rajan, IMRN 2001 no. 12, show the ramified set has density zero but can be
infinite. True for `n = 1`, where the torsion of `1 + 𝔪` is finite and class field
theory closes the argument. This is why "finitely ramified" is an explicit
condition in Fontaine–Mazur rather than a consequence of continuity, and it means
`hunram` is load-bearing rather than a convenience.

**Mathlib survey additions (v4.28.0).**
- `IsArithFrobAt.exists_of_isInvariant` fails at the infinite level on three
  counts, not one: finite residue field, `[Finite G]`, and
  `[Algebra.IsInvariant R S G]`.
- `isPretransitive_of_isGaloisGroup` requires `[Finite G] [IsGaloisGroup G A B]`,
  so transitivity of the action on primes above `v` is unavailable here.
- Chebotarev density is absent from Mathlib entirely.
- `Ideal.inertia G Q = {g | ∀ x, g • x - x ∈ Q}`; since `C ⧸ Q` is integral over
  the field `A ⧸ v` it is a field and equals the residue field of the
  corresponding place of `K̄`, so this is literally the classical inertia group,
  and membership already forces stabilisation of `Q` — no decomposition-group
  clause is needed.

**Not verifiable by review.** Compile status and the axiom audit are attested, not
reproduced; an instance diamond on the supplied `MulSemiringAction` can only be
excluded by a build. Lafforgue VII.6 and Deligne 1.2.10 were checked through
Drinfeld's verbatim quotations, not the paywalled originals.
