# lambda_adic_slice

[![build](https://github.com/SuvirRathore/lambda_adic_slice/actions/workflows/build.yml/badge.svg)](https://github.com/SuvirRathore/lambda_adic_slice/actions/workflows/build.yml)

A statement-level formalisation in Lean 4 of compatible families of λ-adic Galois
representations, and of the statement of Lafforgue's companion theorem for
curves. Five supporting lemmas are proved; the companion theorem is stated and
left `sorry` deliberately. Getting the statement exactly right is the point: a
statement can compile, pass an axiom audit, and still be mathematically false,
and several such errors were found and corrected here.

A secondary purpose is to establish precisely which ingredients Mathlib v4.28.0
supports and which it does not.

Drafted with LLM assistance; every statement was independently audited against
Mathlib v4.28.0 source and the primary literature. AUDIT.md records the Mathlib
survey, the errors corrected, and the claims that remain unverified.

## The slice

Fix a finite field `𝔽_q` of characteristic `p`; a function field `K` over `𝔽_q`
with algebraic closure `K̄` and absolute Galois group `G_K = Gal(K̄/K)`, carrying
the Krull topology; a Dedekind domain `A` which is a finite-type `𝔽_q`-algebra
with fraction field `K`, so that `Spec A` is a smooth affine curve over `𝔽_q` and
the height-one primes of `A` are its closed points, all but finitely many of the
places of `K`; a number field `E` of coefficients, with `λ` ranging over its
finite places, completion `E_λ` and residue characteristic `ℓ(λ)`; a finite set
`S` of places of `A`; an integer `n ≥ 1`; and a choice of Frobenius element
`Frob_v ∈ G_K` at each place `v`.

A family `(ρ_λ)` of continuous homomorphisms `ρ_λ : G_K → GL_n(E_λ)` is a
compatible family unramified outside `S` if for every `v ∉ S` there is a
polynomial `P_v ∈ E[T]` such that for every `λ` with `v ∤ ℓ(λ)`, the
representation `ρ_λ` is unramified at `v` and the characteristic polynomial of
`ρ_λ(Frob_v)` is the image of `P_v`. The polynomial is chosen before `λ`, not
after; that quantifier order is the content of the definition.

Lafforgue's companion theorem, curve case, as formalised here. Let `ℓ(λ₀) ≠ p`
and let `ρ₀ : G_K → GL_n(E_{λ₀})` be continuous, absolutely irreducible, of
finite-order determinant, unramified at every `v ∉ S`, with
`char poly ρ₀(Frob_v) = P_v` for a fixed family `P_v ∈ E[T]`. Then for every
finite place `λ` of `E` with `ℓ(λ) ≠ p` there exist a finite extension `M/E_λ`
and a continuous `ρ : G_K → GL_n(M)`, unramified at every `v ∉ S`, with
`char poly ρ(Frob_v) = P_v` under `E → E_λ → M`, itself absolutely irreducible
with determinant of finite order.

The statement is made one place `λ` at a time. A family indexed by all `λ`
follows by choice and carries the same existence content.

`M` carries the `E_λ`-module topology, via Mathlib's `IsModuleTopology`, rather
than an arbitrary one; that is what makes continuity well-posed. For a finite
extension of the complete field `E_λ` it is the canonical valuation topology, so
the degenerate reading in which every map is continuous is excluded.

## What is proved

`charpoly_eq_of_isConj_gl` and `charpoly_eq_of_isConj`: the characteristic
polynomial of `ρ(g)` depends only on the conjugacy class of `g`. This is not the
well-definedness fact behind the compatibility condition; see below.

`isFrobAt_conj`: conjugates of a Frobenius element at `v` are again Frobenius
elements at `v`, from `IsArithFrobAt.conj`.

`toHom_eq_of_isArithFrobAt`: if `ρ` is unramified at `v` and `g`, `g'` are
Frobenius elements at the same prime `Q` above `v`, then `ρ g = ρ g'`. The
argument runs through inertia: `IsArithFrobAt.mul_inv_mem_inertia` gives
`g * g'⁻¹ ∈ inertia Q`, which `ρ` kills.

`charpoly_eq_of_isArithFrobAt`: the corresponding statement for characteristic
polynomials.

`IsFrobAt` is a definition, not an axiom. It is built on Mathlib's
`IsArithFrobAt` via a `MulSemiringAction` of `G_K` on the integral closure of `A`
in `K̄`. That instance is not in Mathlib and is supplied here; it is the only
obstruction to defining arithmetic Frobenius at the infinite level, since
`IsArithFrobAt` is already stated for monoid actions and needs no finiteness.
Existence is a separate matter, treated under Limitations.

## Absolute irreducibility without algebraic closures

Both the hypothesis on `ρ₀` and the conclusion about the companion need absolute
irreducibility. Formalising that naively means constructing an algebraic closure
of `E_λ`, giving it a topology, and base-changing the representation, none of
which Mathlib v4.28.0 makes cheap.

The slice avoids all of it. `SpanFull ρ` says that the `R`-linear span of the
image of `ρ` is the whole matrix algebra `M_n(R)`. For `R` a field and `n ≥ 1`
this is equivalent to absolute irreducibility, by an argument short enough to
state here. The image contains `1` and is closed under multiplication, so its
span is already an `R`-subalgebra; if that span is `M_n(R)` it remains full after
any scalar extension, so there is no proper nonzero invariant subspace over any
extension field. Conversely, if `ρ` is absolutely irreducible then Burnside's
theorem over an algebraic closure `R̄` gives a span of dimension `n²`, and the
span over `R̄` is `R̄ ⊗_R` the span over `R`, so the span over `R` already has
dimension `n²`.

The equivalence is not formalised; it is what justifies the choice of predicate.
The point is that the predicate mentions no closure, no base change and no
topology, and applies unchanged to the companion over `M`.

Three related remarks, none of them stated in the Lean.

The finite extension can be taken of a specific degree. Drinfeld's Lemma 2.7
(arXiv:1007.4004) is an elementary Brauer-group argument: a semisimple
representation of dimension `r` over an algebraic closure of `E_λ` whose
character is defined over `E_λ` descends to any extension whose degree is
divisible by each of `r, r-1, …, 2`. Its hypothesis is met here, since the
companion is irreducible and its character is defined over `E_λ` because the
Frobenius traces lie in `E ⊆ E_λ`, the Frobenii are dense by Chebotarev in the
quotient through which the companion factors, the trace is continuous, and `E_λ`
is closed in `M`. So `[M : E_λ] = n!` suffices.

Drinfeld's Theorem 1.1 carries a hypothesis that the roots of the characteristic
polynomials are `λ`-adic units. For curves that is a consequence of absolute
irreducibility and finite-order determinant, not an extra assumption, so nothing
has been dropped, but the mechanism is not purity. Being a unit away from `p` is
part (c) of Deligne's Conjecture 1.2.10, a conclusion separate from the weight
condition, and for curves it is part of what Lafforgue's Théorème VII.6 proves.
Purity is the archimedean statement and does not imply integrality: `(3 + 4i)/5`
has absolute value `1` at every archimedean place and is not a `5`-adic unit.

At `λ₀` one may take `M = E_{λ₀}` and `ρ = ρ₀`, so `ρ₀` is itself one of the
companions. No clause asserting this is needed or stated: once the coefficient
field varies, an equality `ρ_{λ₀} = ρ₀` is type-inappropriate.

## Limitations

Deliberately out of scope, and stated because a formalisation that compiles is
not thereby correct.

Frobenius existence is assumed, not proved. `FrobeniusChoice` takes it as data.
Mathlib's `exists_of_isInvariant` fails here on three counts: it requires a
finite residue field at the chosen prime, at `K̄` the algebraic closure of `A/v`;
a finite acting group; and `Algebra.IsInvariant`. Proving existence needs
surjectivity of the decomposition group onto the residue Galois group together
with an inverse-limit or Zorn argument over finite subextensions. The definition
of arithmetic Frobenius transfers to the infinite level; the existence proof does
not. Every result mentioning `FrobeniusChoice` is conditional on it.

`IsFrobAt` silently entails a finite residue field. Mathlib defines
`IsArithFrobAt` by `g · x ≡ x ^ #(A/v) (mod Q)` with `#` read as `Nat.card`. If
`A/v` were infinite that cardinal is `0`, the congruence at `x = 0` forces
`1 ∈ Q`, and primality fails. So there is no degenerate reading, but
`FrobeniusChoice` is uninhabited for any `A` with an infinite residue field, and
every result taking one is then vacuously true.

Frobenius independence is proved only at a fixed prime. Comparing Frobenius
elements at different primes above `v` needs transitivity of the `G_K`-action on
those primes, which is not available here.

There is no descent to `E_λ`. The companion lands in a finite extension `M/E_λ`.
Descent to `E_λ` for the given `E` is false in general, obstructed by the Schur
index in `Br(E_λ)`. Descent after enlarging `E` is Chin, Independence of ℓ in
Lafforgue's theorem, Adv. Math. 180 (2003), which Drinfeld cites for exactly this
step, and is not formalised here.

`HeightOneSpectrum A` indexes an affine model. The places of the proper curve
outside `Spec A` are unconstrained, so unramified outside `S` permits
ramification there. This is not the same as `π₁^ét(X ∖ S)` for projective `X`.

`IsCompatibleFamily` is the `E_λ`-valued notion. It is a legitimate definition
and is kept, but it is not what the companion theorem produces. `IsIrred` is
likewise kept as the `E_λ`-irreducibility notion, and is deliberately not the
hypothesis of `exists_companion`.

The main theorem is `sorry`. Formalising the proof is not in scope.

## Where an earlier version overclaimed

Recorded because the direction of the error matters. Two items above were
previously filed as limitations when they were the opposite, respects in which
the formal statement asserted more than Lafforgue's theorem gives: the conclusion
placed the companions over `E_λ` itself, and the irreducibility hypothesis was
irreducibility over `E_λ`, which is weaker than absolute irreducibility, so using
it strengthened the theorem.

A `sorry` conceals both. A statement that is unprovable because it is false looks
exactly like a statement that is unproved because the infrastructure is missing.

## Formulation, correctness, and future work

The slice is stated via `G_K` with an unramified-outside-`S` condition rather
than via `π₁^ét(X ∖ S)`. Mathlib v4.28.0 has a complete abstract Galois-category
development in `Mathlib/CategoryTheory/Galois/`, but the finite étale site of a
scheme is not instantiated as a Galois category, so no `π₁^ét(X)` is available.

`lake build` verifies that the proofs are valid. It does not verify that the
definitions say what they are intended to say. That gap is the entire risk here,
and it is where every error listed in AUDIT.md was found. CI checks the build and
the axiom profile of every declaration, so the single `sorry` cannot silently
move or multiply. Further review is welcome.

Natural next steps: existence of Frobenius elements in the absolute Galois group,
which is self-contained, currently missing from Mathlib, and a plausible
contribution; coefficient-field descent, which would replace `M` by `E_λ` for a
suitably enlarged `E`; independence of `ℓ` for arithmetic monodromy groups, Chin,
JAMS 17 (2004); and Deligne's conjecture in dimension at least `2`, proved by
Drinfeld.

## Build

Lean v4.28.0 and Mathlib v4.28.0, pinned exactly.
lake exe cache get && lake build
lake env lean Axioms.lean
