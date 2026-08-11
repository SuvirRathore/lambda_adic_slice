# lambda_adic_slice

A statement-level formalisation of one definitional slice from arithmetic
geometry: compatible families of λ-adic Galois representations, and the
statement of Lafforgue's companion theorem for curves.

The purpose is to find out precisely which ingredients Mathlib v4.28.0 supports
and which it does not. The main theorem is stated, not proved. Five supporting
results are proved.

## The slice

Fix:
- `K` a global field with algebraic closure `K̄`, and `G_K = Gal(K̄/K)` its
  absolute Galois group with the Krull topology;
- `A` a Dedekind domain with fraction field `K`, so that `HeightOneSpectrum A`
  indexes the finite places of an affine model;
- `E` a number field (the coefficient field), `λ` ranging over its finite
  places, with completion `E_λ` and residue characteristic `ℓ(λ)`;
- `S` a finite set of places;
- `n ≥ 1`.

**Definition (compatible family).** Given a choice of Frobenius element at each
place, a family `(ρ_λ)_λ` of continuous homomorphisms `ρ_λ : G_K → GL_n(E_λ)`
is a *compatible family unramified outside `S`* if:

1. for every `λ`, `ρ_λ` is unramified at every `v ∉ S` with `v ∤ ℓ(λ)`;
2. for every such `v`, the characteristic polynomial of `ρ_λ(Frob_v)` is the
   image of a polynomial `P_v ∈ E[T]` that does not depend on `λ`.

**Theorem (Lafforgue's companion theorem).** Let `K` be a global function field
and `ℓ(λ₀) ≠ char K`. Let `ρ_{λ₀}` be continuous, irreducible, of finite-order
determinant, unramified outside `S`, and with Frobenius characteristic
polynomials rational over `E`. Then `ρ_{λ₀}` is a member of a compatible family
unramified outside `S`.

## What is proved

- `charpoly_eq_of_isConj_gl`, `charpoly_eq_of_isConj` — the characteristic
  polynomial of `ρ(g)` depends only on the conjugacy class of `g`.
- `isFrobAt_conj` — conjugates of a Frobenius element at `v` are again
  Frobenius elements at `v` (from `IsArithFrobAt.conj`).
- `toHom_eq_of_isArithFrobAt` — if `ρ` is unramified at `v` and `g`, `g'` are
  Frobenius elements at the *same* prime `Q` above `v`, then `ρ g = ρ g'`. The
  argument runs through inertia: `IsArithFrobAt.mul_inv_mem_inertia` gives
  `g * g'⁻¹ ∈ inertia Q`, which `ρ` kills.
- `charpoly_eq_of_isArithFrobAt` — the corresponding statement for
  characteristic polynomials.

`IsFrobAt` is a definition, not an axiom: it is built on Mathlib's
`IsArithFrobAt` via a `MulSemiringAction` of `G_K` on the integral closure of
`A` in `K̄`. That instance is **not** in Mathlib and is supplied here; it turned
out to be the only real obstruction, since `IsArithFrobAt` is already stated for
monoid actions and needs no finiteness.

## Limitations

Stated explicitly, because a formalisation that compiles is not thereby correct.

- **Frobenius existence is assumed, not proved.** `FrobeniusChoice` takes it as
  data. Mathlib's `exists_of_isInvariant` requires a finite residue field at the
  chosen prime; at `K̄` that residue field is the algebraic closure of `A/v`, so
  the proof does not transfer. Proving it needs surjectivity of the
  decomposition group onto the residue Galois group plus an inverse-limit or
  Zorn argument over finite subextensions. The *definition* of arithmetic
  Frobenius transfers to the infinite level; the existence *proof* does not.
- **Frobenius independence is proved only at a fixed prime.** Comparing
  Frobenius elements at different primes above `v` needs transitivity of the
  `G_K`-action on primes above `v`, which is not available here.
- **`IsIrred` is irreducibility over `E_λ`**, not absolute irreducibility. The
  base change to an algebraic closure of `E_λ` is not formalised.
- **No coefficient-field descent.** The conclusion places the companions over
  `E_λ` itself. Lafforgue's theorem gives companions over finite extensions of
  `E_λ`; descending to a common number field is Chin's theorem and is not
  formalised here.
- **`HeightOneSpectrum A` indexes an affine model.** For `K = 𝔽_q(t)` and
  `A = 𝔽_q[t]` the place at infinity is omitted, so "unramified outside `S`"
  permits ramification there. This is not the same as `π₁^ét(X ∖ S)` for
  projective `X`.
- **The main theorem is `sorry`.** Formalising the proof is not in scope.

## Note on formulation

Stated via `G_K` with an unramified-outside-`S` condition rather than via
`π₁^ét(X ∖ S)`. Mathlib v4.28.0 has a complete abstract Galois-category
development (`Mathlib/CategoryTheory/Galois/`), but the finite étale site of a
scheme is not instantiated as a Galois category, so no `π₁^ét(X)` is available.

## Correctness

`lake build` verifies that the proofs are valid. It does not verify that the
definitions say what they are intended to say. An independent review of an
earlier version found four substantive errors, all of which had compiled: a
false axiom asserting that Frobenius lifts at a place are conjugate (they differ
by inertia); a well-definedness claim that the proved lemmas did not support; a
main theorem missing the hypotheses that make it true; and a vacuity hole where
Frobenius existence was never actually assumed. Those are fixed. Further review
is welcome — see `CAPABILITY_LOG.md`.

## Future work

- Deligne's conjecture for function fields of normal varieties of finite type
  over a finite field of dimension ≥ 2, where the index set is closed points
  rather than places — proved by Drinfeld.
- Chin + Drinfeld independence-of-`ℓ` for arithmetic monodromy groups.
- Existence of Frobenius elements in the absolute Galois group — self-contained,
  currently missing from Mathlib, and a plausible contribution.

## Build

Lean v4.28.0, Mathlib v4.28.0 (pinned for Aristotle compatibility).
lake exe cache get && lake build
