# Audit record

`lake build` kernel-checks the proofs that are given, accepting `sorry` as an
axiom; it says nothing about whether the definitions mean what they claim. This
file records what Mathlib v4.28.0 could and could not supply, the errors found,
and which claims are not machine-checked.

## Mathlib v4.28.0

Everything below was verified by reading source at the pinned tag rather than
from recall, claims of absence included; both kinds have been got wrong here at
least once.

Available: `krullTopology` on `Gal(L/K)`; `IsDedekindDomain.HeightOneSpectrum`
and `.adicCompletion`; `GL`; `Matrix.charpoly` and `Matrix.charpoly_units_conj`;
`RingTheory/Frobenius.lean`, whose `IsArithFrobAt` is stated for monoid actions
with `SMulCommClass` and needs no finiteness; `Ideal.inertia`;
`IsArithFrobAt.mul_inv_mem_inertia`; `IsArithFrobAt.conj`;
`Topology/Algebra/Module/ModuleTopology.lean`, which is what makes a coefficient
field finite over `E_λ` expressible with a pinned rather than an arbitrary
topology; `Algebra.FiniteType`; the `MulSemiringAction` of a group on
`integralClosure R K` together with its `SMulCommClass`, in
`RingTheory/IntegralClosure/Algebra/Basic.lean`, which with
`AlgEquiv.applyMulSemiringAction` and `AlgEquiv.apply_smulCommClass'` give the
action of `G_K` on the integral closure with nothing to supply by hand; and
`CategoryTheory/Galois/` as an abstract development.

Partial: `NumberTheory/FunctionField.lean` gives the predicate and the valuations
but no tie-in to a curve. Unramifiedness predicates exist, but nothing for a
representation.

Missing: `π₁^ét(X)` for schemes. The Galois-category development is abstract,
with finite `G`-sets as its only worked instance. Both the big étale site and the
small one, on the category of schemes étale over `X`, exist as Grothendieck
topologies in `AlgebraicGeometry/Sites/Etale.lean`, together with a geometric
point `geometricFiber` of the big étale topology at a separably closed field.
What is absent is the finite
étale subcategory, a fibre functor on it, and the Galois-category instance
joining the two developments. This decided the `G_K`-based formulation.
Chebotarev density is absent entirely, as is characteristic-polynomial
coefficient descent to `E`.

Three facts about the Frobenius API constrain the design.

`IsArithFrobAt R g Q` unfolds to `∀ x, g • x - x ^ Nat.card (R ⧸ Q.under R) ∈ Q`.
If the base residue ring were infinite that cardinal is `0`, the congruence at
`x = 0` gives `1 ∈ Q`, and primality fails; Mathlib
records this as `AlgHom.IsArithFrobAt.finite_quotient`. So there is no
degenerate `q = 0`
reading, but a Frobenius choice is uninhabited whenever a residue field is
infinite, and every result taking one is then vacuously true.

`IsArithFrobAt.exists_of_isInvariant` fails at the infinite level on three
counts: a finite residue field at the chosen prime, `[Finite G]`, and
`[Algebra.IsInvariant R S G]`. Existence of Frobenius elements in the absolute
Galois group therefore has to be assumed as data. The same file carries a fuller
finite-level theory: a canonical `arithFrobAt` and conjugacy of the canonical
Frobenii at primes over one base prime (`isConj_arithFrobAt`, via
`exists_primesOver_isConj`), both under the same finiteness and invariance
hypotheses, and uniqueness under unramifiedness
(`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`), an `AlgHom`-level statement whose
hypotheses are instead Noetherianity of the top ring and `Algebra.IsUnramifiedAt`
at the prime. None of it transfers: the first two for the group-finiteness
reasons above, the third because the integral closure in `K̄` is not
Noetherian; its `Algebra.IsUnramifiedAt` hypothesis in fact holds there, the
integral closure being perfect in characteristic `p`.

`isPretransitive_of_isGaloisGroup` requires `[Finite G]` and
`[IsGaloisGroup G A B]`. `RingTheory/Invariant/Profinite.lean` removes the
finiteness: `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` gives
transitivity on the primes over a base prime for a profinite group acting
continuously on a discrete ring, and
`Ideal.Quotient.stabilizerHom_surjective_of_profinite` surjects the stabilizer
of a prime onto the residue Galois group. Both carry `Algebra.IsInvariant`,
which fails for `G_K` on the integral closure in `K̄`: the invariants are the
integral elements of the purely inseparable closure of `K`, not `A`. A
derivation over the separable closure, transferred along the purely inseparable
extension, is not carried out here, which is why Frobenius independence is
proved only at a fixed prime.

## Errors found and corrected

All of the following compiled cleanly and passed `#print axioms`; they were found
by independent review of the definitions themselves. They are ordered by severity.

The most serious were false statements. An axiom asserted that any two Frobenius
elements at a place are conjugate, when in fact two lifts at the same prime
differ by an element of inertia; it was deleted and replaced by the correct
inertia argument. The companion statement was false as first written, since a
rank-one unramified character of the constant-field quotient has Frobenius
eigenvalues outside `E`. Absolute irreducibility, finite-order determinant and
`E`-rationality of the Frobenius characteristic polynomials were all added. The
first two are Lafforgue's own hypotheses; the third is an artefact of fixing `E`
in advance here, where Lafforgue obtains the number field as part of the theorem.
Neither of the first two is necessary for a compatible family to exist, since
reducible compatible systems do; the third cannot be dropped even in principle,
because the notion of compatibility here builds `E`-rationality of the
polynomials into the definition.
Once those hypotheses were added the statement was still stronger than the
theorem it named, in two independent ways. The conclusion placed companions over
`E_λ` itself, where Theorem VII.6(v) gives the companion over a finite extension
of `E_λ` and descent to `E_λ` for a fixed `E` is obstructed by the class of a
central simple algebra in `Br(E_λ)`. Chin's theorem is the stronger uniform
coefficient-field descent, available after enlarging `E`. The irreducibility hypothesis was irreducibility over `E_λ`, which is
weaker than absolute irreducibility, so using it strengthened the theorem. Both
had been recorded as limitations; in fact each made the statement assert more,
not less.

Next were two ways the statement could hold without content. Frobenius existence
was never actually assumed, since declaring a structure with an existence field
does not assume it, so the compatibility condition could hold vacuously; it is
now passed as data. Separately, the base ring was an arbitrary Dedekind domain
with the right fraction field, and fields and discrete valuation rings qualify,
so the place set could be empty or a single point. In the empty case every condition in the
definition quantifies over places that do not exist, and the conclusion was
trivially satisfiable; a single place leaves the compatibility conditions
constraining one Frobenius conjugacy class instead of infinitely many. This file previously claimed an explicit cheap witness in the one-place
case, a companion-matrix representation of the constant-field quotient. That was
overstated: the construction is guaranteed to match the prescribed
polynomial only at a place of degree one: a place of degree `d` sends the generator to the
`d`-th power of the chosen matrix, and equality of the characteristic
polynomials then generally fails. It also needs the roots of the polynomial to
be units at the target `λ`, which continuity supplies only at `λ₀`. Nor would any witness
of that shape survive the present conclusion: a representation factoring through
a procyclic group has image generated by a single matrix `C`, so its span lies
in `M[C]` and has dimension at most `n`, short of the `n²` that `SpanFull`
demands once `n > 1`. Requiring the
base ring to be a finite-type algebra over the chosen finite base field rules
out the discrete valuation rings, and the compatible embedding of `Fq(t)` into
the fraction field rules out the finite fields, which are finite-type with empty
spectrum; together they make the spectrum a smooth affine curve carrying
cofinitely many of the places, and close this.

Three claims were described as doing more than they do.
`charpoly_eq_of_isConj` was said to establish well-definedness of the
compatibility condition, which needs inertia rather than conjugacy, and a
docstring continued to assert that claim, and to cite the deleted axiom, after
the code had been corrected. Unit-ness of the Frobenius roots away from `p` was attributed to purity, when it is part (iii) of Deligne's Conjecture 1.2.10, labelled (c) in
Drinfeld's abbreviated restatement, proved for curves by Lafforgue, and a conclusion separate from the weight condition; `(3 + 4i)/5` has
absolute value `1` at every archimedean place and is not a `5`-adic unit. The
equivalence between the span condition and absolute irreducibility was stated
without its scope, which is a field and `n ≥ 1`.

Two smaller items were reformulations rather than corrections of wrong
mathematics. Positivity of `n` became a hypothesis of the main theorem; the
definitions still compile at `n = 0`, where `GL (Fin 0)` is trivial and the
predicates hold vacuously, harmless where they are used. And unramifiedness,
which had quantified over one prime above a place, now quantifies over every
prime; the two readings are equivalent once a prime above `v` exists, since the
primes are conjugate and `ker ρ` is normal, but the every-prime form does not
lean on the transitivity that is unavailable here.

One error was not about the mathematics at all. An action of `G_K` on the
integral closure of `A` in `K̄`, and the `SMulCommClass` accompanying it, were
declared here and documented in three places as absent from Mathlib. Both are in Mathlib v4.28.0, and both resolve in this file's own context without help, so the
hand-written versions were shadowing them. The claim came from an early survey
and was repeated without reading the source. A claim of absence is not a
mathematical claim, and review aimed at the mathematics does not test it. The instances are deleted
and the file builds on Mathlib's. A related inventory error in the same area, an
undercount of what the étale-site file contains, was corrected at the same time;
the conclusion it supported, that no `π₁^ét(X)` is available, survives.

## What is not machine-checked

Compile status, the axiom profile, and the count of `sorry` lines are checked
in CI; see `Axioms.lean` and
`.github/workflows/build.yml`. The axiom check pins the set of axiom names in each named declaration's
dependency closure. On its own that misses two things: a `sorry` in a
declaration outside those closures, and a second `sorry` inside a closure
already reporting `sorryAx`, since the set of names does not change; `lake
build` accepts both with only a warning. CI therefore also counts the source lines consisting of `sorry` and requires
exactly one, which closes both when the `sorry` stands on its own line; a
`sorry` inlined into a tactic block in either place would still pass. The one admitted declaration is
`exists_companion`; `exists_companion_family` is proved and inherits its
`sorryAx`. No instances are declared on types Mathlib owns; the five instances declared here are the
projections of `CompanionRep`, whose carrier is defined here.

Five notions defined here have close Mathlib counterparts that are not used.
`LambdaAdicRep` is a `ContinuousMonoidHom`; the recurring conjunction
`Q.IsPrime ∧ Q.under A = v.asIdeal` is membership in `Ideal.primesOver`, the
idiom `RingTheory/Frobenius.lean` itself uses, where `Ideal.LiesOver` alone
records only the contraction equality; `Field.absoluteGaloisGroup` is the
fixed-closure form of `AbsGal`; `IsIrred` is a matrix presentation of
`Representation.IsIrreducible`; and `DetFiniteOrderHom` applied to `ρ` says
`IsOfFinOrder` of the composite of `Matrix.GeneralLinearGroup.det` with `ρ`.
Each matches what is written over the field-valued, positive-dimension setting
used here, and most would be the better choice in a revision;
`Field.absoluteGaloisGroup` fixes the closure `AlgebraicClosure K`, where the
parameterised `Kbar` is used throughout. Three further
items: `IsUnramifiedAt` is hard-wired to representations over `E_λ`, so the same
inertia condition is written a second time, inline, in the conclusion of
`exists_companion`, where a version stated for an arbitrary `G →* GL n R` would
let hypothesis, conclusion and the family corollary share one predicate; `FrobeniusChoice` supplies a lift at every place
where only the places outside `S` are used; and the file imports the whole of
Mathlib, where explicit imports would record its actual dependencies. Section
instance variables enter a definition only when it uses them, so the definitions
here are stated over a bare commutative ring, and the Dedekind, fraction-field
and algebraic-closure setting the README fixes binds only in the theorems, which
include it automatically. The two companion theorems match the README's
frame exactly; the supporting lemmas omit hypotheses they do not use, and
`IsCompatibleFamily`, which no theorem consumes, never regains that
setting and is that much more general than its prose.

I checked the literature attributions, including Deligne's part-numbering in
Weil II and the hypotheses and conclusions of Lafforgue's Theorem VII.6, against
the primary sources. Two asides rest on standard usage rather than the
original papers: the attribution of the matrix-span criterion to Burnside, and
the remark about the Fontaine–Mazur conjecture.

Mathematical claims in the prose are not machine-checked; the compiled theorems
are listed in the README.

## Adversarial probes

I probed the statement with an automated theorem prover, Aristotle, which
searches for any proof a statement admits, including the proofs that exist only
because the statement is broken. Asked to fill the `sorry` in
`exists_companion`, it attacked the statement rather than the mathematics: it
looked for a contradiction in the hypothesis package, a degenerate model, a
trivial companion, an escape at `n = 0`, and a transport of `ρ₀` along an
abstract field isomorphism. Every attack failed where this record says it
should. It derived that the base ring cannot be a field, a finite-type algebra
over a finite field that is a field being finite while `Fq(t)` embeds in the
fraction field, and that a trivial companion forces `P v = (X - 1)^n` at
infinitely many places against a finite `S`. No field embedding connects
completions of distinct residue characteristics, which closed the transport
route. It checked in Lean that the Galois action underlying `IsFrobAt` is the
genuine one, and it returned the repository unmodified, concluding that the
residual content of the `sorry` is the companion-existence theorem itself. It
had this repository's documentation available, so that reading is not
independent testimony; the failed attacks are.

The definitions got the same treatment. I submitted `SpanFull` for the trivial
two-dimensional representation as a target; the statement is false, since the
span of the identity is the scalar line, and a definition of absolute
irreducibility that a prover can satisfy for a reducible representation would
be broken. The prover declined to prove it and proved its negation instead,
exhibiting a matrix outside the span. The definition held with its own failure
mode as the target.

The third probe asked for a term of `FrobeniusChoice`, the one ingredient this
repository assumes, and the prover constructed it. Mathlib v4.28.0's profinite
invariant theory applies over the separable closure, where `A` is the ring of
invariants of the integral closure; the obstruction recorded above, that the
invariants over `K̄` contain the purely inseparable elements as well, is absent
there. The arithmetic Frobenius it produces lifts to `Aut(K̄/K)` because
`K̄/Ks` is purely inseparable. I audited the proof against the pinned source
and checked it with the kernel; it depends only on `propext`,
`Classical.choice` and `Quot.sound`. The construction is not part of this
repository: `FrobeniusChoice` remains data here and every result conditional on
it stays conditional. What the probe changes is the status of the assumption,
from open to constructible at the pinned Mathlib.
