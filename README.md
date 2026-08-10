# lambda_adic_slice

Statement-level formalisation of one definitional slice from arithmetic geometry.
Statements only: every proof is `sorry`. The point is to locate which ingredients
Mathlib v4.28.0 currently supports and which are missing.

## The slice

Fix:
- `K` a global field and `K̄` an algebraic closure, `G_K = Gal(K̄/K)` its absolute
  Galois group equipped with the Krull topology;
- `E` a number field (the coefficient field), `λ` ranging over finite places of `E`,
  with completion `E_λ` and residue characteristic `ℓ(λ)`;
- `S` a finite set of finite places of `K`;
- `n ≥ 1` an integer.

**Definition (compatible family).** A family `(ρ_λ)_λ` of continuous homomorphisms
`ρ_λ : G_K → GL_n(E_λ)` is a *compatible family unramified outside `S`* if:

1. for every `λ`, `ρ_λ` is unramified at every finite place `v` of `K` with
   `v ∉ S` and `v ∤ ℓ(λ)`;
2. for every such `v`, the characteristic polynomial of `ρ_λ(Frob_v)` has
   coefficients in `E` (via a fixed embedding `E ↪ E_λ`) and is independent of `λ`.

**Theorem (Deligne's conjecture for curves; L. Lafforgue).** Suppose `K` is a global
function field, i.e. the function field of a smooth projective curve over a finite
field, and `ℓ(λ) ≠ char K`. Then every continuous `λ`-adic representation
`ρ_λ : G_K → GL_n(E_λ)` unramified outside `S` is a member of a compatible family
unramified outside `S`.

## Note on formulation

Stated via `G_K` with an unramified-outside-`S` condition rather than via
`π₁^ét(X ∖ S)`. These agree for a smooth projective curve `X` with function field `K`,
and the `G_K` formulation is the one Mathlib v4.28.0 can plausibly express: Galois
categories and fibre functors exist abstractly (`Mathlib/CategoryTheory/Galois/`),
but the finite étale site of a scheme is not instantiated as a Galois category, so
there is no `π₁^ét(X)` available.

## Future work (currently out of scope)

- Deligne's conjecture for `K` the function field of a normal variety of finite type
  over a finite field (dimension ≥ 2), where the index set is closed points of the
  variety rather than places of `K` — proved by Drinfeld.
- Chin + Drinfeld independence-of-`ℓ` for arithmetic monodromy groups. Requires
  algebraic-group infrastructure well beyond this slice.

## Build

Lean v4.28.0, Mathlib v4.28.0 (pinned for Aristotle compatibility).
`lake exe cache get && lake build`
