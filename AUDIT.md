# Audit record

`lake build` verifies that proofs are valid. It says nothing about whether the
definitions mean what they claim. For a statement-level formalisation that gap is
the entire risk, so this file records what Mathlib v4.28.0 could and could not
supply, which errors were found in the course of the work, and which claims here
are not machine-checked.

## Mathlib v4.28.0

Everything below was verified by reading source at the pinned tag rather than
from recall, claims of absence included. Those are the easiest kind to leave
unchecked, and both kinds have been got wrong here at least once; see below.

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
topologies in `AlgebraicGeometry/Sites/Etale.lean`. What is absent is the finite
étale subcategory, a fibre functor on it, and the Galois-category instance
joining the two developments. This decided the `G_K`-based formulation.
Chebotarev density is absent entirely, as is characteristic-polynomial
coefficient descent to `E`.

Three facts about the Frobenius API constrain the design.

`IsArithFrobAt R g Q` unfolds to `∀ x, g • x - x ^ Nat.card (R ⧸ Q.under R) ∈ Q`.
If the base residue ring were infinite that cardinal is `0`, the congruence at
`x = 0` gives `1 ∈ Q`, and primality fails. So there is no degenerate `q = 0`
reading, but a Frobenius choice is uninhabited whenever a residue field is
infinite, and every result taking one is then vacuously true.

`IsArithFrobAt.exists_of_isInvariant` fails at the infinite level on three
counts, not one: a finite residue field at the chosen prime, `[Finite G]`, and
`[Algebra.IsInvariant R S G]`. Existence of Frobenius elements in the absolute
Galois group therefore has to be assumed as data.

`isPretransitive_of_isGaloisGroup` requires `[Finite G]` and
`[IsGaloisGroup G A B]`, so transitivity of the action on primes above a place is
unavailable, which is why Frobenius independence is proved only at a fixed prime.

## Errors found and corrected

All of the following compiled cleanly and passed `#print axioms`; they were found
on further review of the definitions themselves. They are ordered by severity.

The most serious were false statements. An axiom asserted that any two Frobenius
elements at a place are conjugate, when in fact two lifts at the same prime
differ by an element of inertia; it was deleted and replaced by the correct
inertia argument. The companion statement was false as first written, since a
rank-one unramified character of the constant-field quotient has Frobenius
eigenvalues outside `E`. Absolute irreducibility, finite-order determinant and
`E`-rationality of the Frobenius characteristic polynomials were all added. The
first two are Lafforgue's own hypotheses; the third is an artefact of fixing `E`
in advance here, where Lafforgue obtains the number field as part of the theorem.
None of the three is necessary for a compatible system to exist, since reducible
ones do.
Once those hypotheses were added the statement was still stronger than the
theorem it named, in two independent ways. The conclusion placed companions over
`E_λ` itself, where Theorem VII.6(v) gives the companion over a finite extension
of `E_λ` and descent to `E_λ` for a fixed `E` is obstructed by the class of a
central simple algebra in `Br(E_λ)`. Chin's theorem is the stronger uniform
coefficient-field descent, available after enlarging `E`. The irreducibility hypothesis was irreducibility over `E_λ`, which is
weaker than absolute irreducibility, so using it strengthened the theorem. Both
had been filed as limitations, which reads as having proved less when the truth
was that it asserted more.

Next were two ways the statement could hold without content. Frobenius existence
was never actually assumed, since declaring a structure with an existence field
does not assume it, so the compatibility condition could hold vacuously; it is
now passed as data. Separately, the base ring was an arbitrary Dedekind domain
with the right fraction field, and fields and discrete valuation rings qualify,
so the place set could be empty or a single point. The conclusion was then
satisfiable cheaply, since the roots of the prescribed polynomial are `λ`-adic
units, `GL_n(O_λ)` is profinite and `Ẑ` is procyclic, so a companion-matrix
representation of the constant-field quotient satisfies everything. What made
that sufficient is that the conclusion of the version in question imposed no
irreducibility on the members of the family. It would not satisfy the present
conclusion: a representation factoring through a procyclic group has image
generated by a single matrix `C`, so its span lies in `M[C]` and has dimension at
most `n`, short of the `n²` that `SpanFull` demands once `n > 1`. Requiring the
base ring to be a finite-type algebra over the constant field makes its spectrum
a smooth affine curve carrying cofinitely many of the places, and closes this.

Three claims were described as doing more than they do.
`charpoly_eq_of_isConj` was said to establish well-definedness of the
compatibility condition, which needs inertia rather than conjugacy, and a
docstring continued to assert that claim, and to cite the deleted axiom, after
the code had been corrected. Unit-ness of the Frobenius roots was attributed to
purity, when it is part (iii) of Deligne's Conjecture 1.2.10, labelled (c) in
Drinfeld's abbreviated restatement, proved for curves by Lafforgue, and a conclusion separate from the weight condition; `(3 + 4i)/5` has
absolute value `1` at every archimedean place and is not a `5`-adic unit. The
equivalence between the span condition and absolute irreducibility was stated
without its scope, which is a field and `n ≥ 1`.

Two smaller defects: `n : ℕ` admitted `n = 0`, and unramifiedness quantified over
one prime above a place where every prime is wanted.

One error was not about the mathematics at all. An action of `G_K` on the
integral closure of `A` in `K̄`, and the `SMulCommClass` accompanying it, were
written by hand and documented in three places as absent from Mathlib and
supplied here. Both are in Mathlib v4.28.0, in the general form a maintainer
would ask for, and both resolve in this file's own context without help, so the
hand-written versions were shadowing them. The claim came from an early survey
and was repeated without reading the source. It survived every review, because a
claim that something is missing from a library is not a mathematical claim and
nothing in the reviews was aimed at that kind of claim. The instances are deleted
and the file builds on Mathlib's. A related inventory error in the same area, an
undercount of what the étale-site file contains, was corrected at the same time;
the conclusion it supported, that no `π₁^ét(X)` is available, survives.

## Why the unramifiedness hypothesis is not redundant

It is tempting to drop it. Continuity forces the image into a compact subgroup of
`GL_n(E_λ)`, which stabilises a lattice, so the representation modulo each power
of the maximal ideal factors through a finite extension ramified at finitely many
places. That gives a finite ramification set at every finite level, but the
level-wise sets need not stabilise, and for `n ≥ 2` they need not. For
`ℓ ≠ char K`, a Kummer class built from `b_m = ∏_{i ≤ m} π_i^{ℓ^i}`, with places
`v_i` and elements `π_i` chosen so that `v_i(π_i) = 1` and each later `π_j` is a
unit at the earlier `v_i`, gives a continuous upper-triangular
`ρ = (χ_ℓ, c; 0, 1) : G_K → GL₂(ℤ_ℓ)` ramified at every `v_i`. Ramakrishna,
*Infinitely ramified Galois representations*, Ann. of Math. 151 (2000), 793–815,
constructs over `ℚ` surjective `GL₂(ℤ_ℓ)`-valued representations ramified at
infinitely many primes, so even full image is compatible with infinite
ramification;
Khare–Rajan, Int. Math. Res. Not. 2001, no. 12, 601–607, show that for continuous
semisimple representations of the absolute Galois group of a number field the
ramified set has density zero while remaining possibly infinite, and remark that
the same holds over function fields when the coefficient residue characteristic
differs from the field characteristic. Semisimplicity is essential there; the
Kummer representations above are not semisimple. For `n = 1` the claim is true,
since the torsion of `1 + 𝔪` is finite and class field theory closes the
argument.

The example settles continuity alone. It does not show the hypothesis independent
of the others: the representation displayed is reducible, so it fails `SpanFull`,
and its determinant `χ_ℓ` has infinite order. Whether continuity together with
absolute irreducibility and finite-order determinant forces finite ramification is
not settled here. The hypothesis is stated because nothing available establishes
that it can be dropped, which is also why finite ramification is an explicit
condition in the Fontaine–Mazur conjecture rather than a consequence of
continuity.

## What is not machine-checked

Compile status and the axiom profile are checked in CI; see `Axioms.lean` and
`.github/workflows/build.yml`. The axiom check covers the declarations named
there and their dependency closures; a `sorry` in a declaration outside those
would not be caught, since `lake build` exits successfully on the warning it
emits. No instances are declared on types Mathlib owns, so the diamond an earlier
version created no longer arises; the five instances declared here are the
projections of `CompanionRep`, whose carrier is defined here.

Three notions defined here have close Mathlib counterparts that are not used.
`LambdaAdicRep` is a `ContinuousMonoidHom`; the recurring conjunction
`Q.IsPrime ∧ Q.under A = v.asIdeal` restates `Ideal.LiesOver`, the idiom
`RingTheory/Frobenius.lean` itself uses; and `Field.absoluteGaloisGroup` is the
fixed-closure form of `AbsGal`. Each is equivalent to what is written, and each
would be the better choice in a version aimed at upstreaming.

Lafforgue's Theorem VII.6 and Deligne's Conjecture 1.2.10 were verified through
Drinfeld's verbatim quotations and bibliography rather than the originals. The
internal part-numbering of the conjecture in Weil II was not checked against
Deligne's own text.

Every mathematical claim in this repository that is not a compiled Lean theorem
is a claim, not a fact. The compiled theorems are listed in the README.
