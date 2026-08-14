/-
Copyright (c) 2026 Suvir Rathore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suvir Rathore
-/
/-
Statement-level formalisation: compatible families of λ-adic Galois
representations, and the companion-existence statement of Lafforgue's theorem
for curves.

Five supporting results are proved. The companion theorem is stated with its
proof left `sorry`, and the family over all coefficient places is derived from
it by choice, inheriting that `sorry`. Existence of Frobenius elements in the absolute
Galois group, which Mathlib v4.28.0 does not provide, is taken as explicit data
and documented as such.
-/
import Mathlib

open IsDedekindDomain NumberField Matrix Polynomial

namespace LambdaAdicSlice

section Setup

-- `A` is a Dedekind domain with fraction field `K`. Its height-one primes are the
-- places carried by the chosen model: for `A = 𝓞 K` they are the finite places of
-- a number field, and for a finite-type Dedekind model of a function field they
-- are the closed points of the corresponding affine curve, hence all but finitely
-- many places of the proper curve. For an arbitrary Dedekind domain with
-- fraction field `K` they need not be either, since Mathlib's `IsDedekindDomain`
-- admits localisations, discrete valuation rings and fields.
-- `exists_companion` imposes the finite-type
-- hypothesis that pins this down.
variable (A K : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]

-- A fixed algebraic closure of `K`.
variable (Kbar : Type*) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]

/-- The automorphism group of `Kbar` over `K`. The abbreviation itself asks only
for an extension; in the companion theorems the ambient `IsAlgClosure K Kbar`
hypothesis makes this the absolute Galois group `G_K`, and the supporting
lemmas omit hypotheses they do not use. The
Krull topology instance comes from `Mathlib/FieldTheory/KrullTopology.lean`. -/
abbrev AbsGal := Kbar ≃ₐ[K] Kbar

-- The coefficient field `E`.
variable (E : Type*) [Field E] [NumberField E]

/-- Finite places of `E`. -/
abbrev CoeffPlace := HeightOneSpectrum (𝓞 E)

/-- The completion `E_λ`. -/
abbrev Completion (lam : CoeffPlace E) := lam.adicCompletion E

variable (n : ℕ)

/-- A `λ`-adic representation: a continuous homomorphism `G_K → GL_n(E_λ)`. -/
structure LambdaAdicRep (lam : CoeffPlace E) where
  toHom : AbsGal K Kbar →* GL (Fin n) (Completion E lam)
  continuous_toHom : Continuous toHom

end Setup

section CharpolyConj

/-- Conjugate elements of `GL m R` have the same characteristic polynomial.

Proved, not assumed. Stated over an abstract `CommRing` so that elaboration
does not have to work inside a completion. -/
theorem charpoly_eq_of_isConj_gl {R : Type*} [CommRing R] {m : ℕ}
    {x y : GL (Fin m) R} (h : IsConj x y) :
    (x : Matrix (Fin m) (Fin m) R).charpoly
      = (y : Matrix (Fin m) (Fin m) R).charpoly := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  simp only [Units.val_mul]
  exact (Matrix.charpoly_units_conj c _).symm

variable (A K : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
variable (Kbar : Type*) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)

set_option maxHeartbeats 1000000 in
-- `Completion E lam` is a `UniformSpace.Completion`; unification inside it is
-- expensive and the default heartbeat budget is insufficient.
omit [IsAlgClosure K Kbar] in
/-- The characteristic polynomial of `ρ(g)` depends only on the conjugacy class
of `g`.

This is not the well-definedness fact behind the compatible-family
condition. Two Frobenius elements at the same prime `Q` above a place need not be
conjugate: they differ by an element of the inertia at `Q`. Across different
primes above one place, a conjugation moves the prime first. The correct argument is
`toHom_eq_of_isArithFrobAt` below, which runs through `Ideal.inertia`. -/
theorem charpoly_eq_of_isConj
    {lam : CoeffPlace E} (rho : LambdaAdicRep K Kbar E n lam)
    {g g' : AbsGal K Kbar} (h : IsConj g g') :
    (rho.toHom g : Matrix (Fin n) (Fin n) (Completion E lam)).charpoly
      = (rho.toHom g' : Matrix (Fin n) (Fin n) (Completion E lam)).charpoly := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine charpoly_eq_of_isConj_gl (isConj_iff.mpr ⟨rho.toHom c, ?_⟩)
  rw [← hc]
  simp [map_mul, map_inv]

end CharpolyConj

section FrobeniusConcrete

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]

/-- The integral closure of `A` in `K̄`. -/
abbrev IntClosure := integralClosure A Kbar

end FrobeniusConcrete

section FrobeniusDefined

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]

/-- `g : G_K` is a **Frobenius at `v`** if there is a prime `Q` of the integral
closure of `A` in `K̄` lying over `v` at which `g` is an arithmetic Frobenius in
Mathlib's sense (`IsArithFrobAt`).

This is a definition, not an axiom: it uses `Mathlib/RingTheory/Frobenius.lean`
directly. The `MulSemiringAction` of `G_K` on the integral closure that
`IsArithFrobAt` requires, and the `SMulCommClass` accompanying it, are supplied by
Mathlib — `AlgEquiv.applyMulSemiringAction`, `AlgEquiv.apply_smulCommClass'`, and
the instances in `RingTheory/IntegralClosure/Algebra/Basic.lean` — and resolve
here with nothing added by hand.

Note that this predicate silently entails finiteness of the residue field
`A ⧸ v`. Mathlib defines `IsArithFrobAt` by `g • x ≡ x ^ #(A ⧸ v) (mod Q)` with
`#` read as `Nat.card`; if `A ⧸ v` is infinite that cardinal is `0`, the
congruence at `x = 0` forces `1 ∈ Q`, and `Q.IsPrime` fails; Mathlib records
this as `AlgHom.IsArithFrobAt.finite_quotient`. So there is no
degenerate `q = 0` reading, but `FrobeniusChoice` below is uninhabited for any
`A` with an infinite residue field, and every result taking one is then
vacuously true. -/
def IsFrobAt (v : HeightOneSpectrum A) (g : AbsGal K Kbar) : Prop :=
  ∃ Q : Ideal (IntClosure A Kbar), Q.IsPrime ∧ Q.under A = v.asIdeal ∧
    IsArithFrobAt A g Q

end FrobeniusDefined

section FrobeniusProperties

open scoped Pointwise

variable {A K Kbar : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]

omit [IsDedekindDomain A] [IsFractionRing A K] [IsAlgClosure K Kbar] in
/-- Conjugates of a Frobenius element at `v` are again Frobenius elements at `v`.

Proved from `IsArithFrobAt.conj`: conjugating the automorphism moves the prime
`Q` to `x • Q`, which still lies over `v`. -/
theorem isFrobAt_conj {v : HeightOneSpectrum A} {g x : AbsGal K Kbar}
    (h : IsFrobAt A K Kbar v g) : IsFrobAt A K Kbar v (x * g * x⁻¹) := by
  obtain ⟨Q, hQp, hQu, hQf⟩ := h
  refine ⟨x • Q, ?_, ?_, hQf.conj x⟩
  · exact hQp.smul x
  · rw [← hQu]
    exact Ideal.under_smul A Q x

end FrobeniusProperties

section ConcreteConditions

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)

/-- The residue characteristic `ℓ(λ)` of a finite place of `E`. -/
noncomputable def resChar (lam : CoeffPlace E) : ℕ := ringChar (𝓞 E ⧸ lam.asIdeal)

/-- `v ∤ ℓ(λ)`: the residue characteristic of `λ` is not in the prime `v`.

In the function-field case this is equivalent to `ℓ(λ) ≠ char K`, since any
prime different from `char K` is a unit in `A`. -/
def NotDividing (v : HeightOneSpectrum A) (lam : CoeffPlace E) : Prop :=
  (resChar E lam : A) ∉ v.asIdeal

end ConcreteConditions

section FrobeniusChoice

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]

/-- A choice of Frobenius element at every finite place.

Existence of Frobenius elements in the *absolute* Galois group is not available
in Mathlib v4.28.0. `IsArithFrobAt.exists_of_isInvariant` fails at `K̄` on three
counts: it requires a finite residue field at the chosen prime (at `K̄`
that field is the algebraic closure of `A/v`), a finite acting group, and
`Algebra.IsInvariant`. Mathlib's profinite
machinery (`RingTheory/Invariant/Profinite.lean`) supplies the
decomposition-group surjectivity and the inverse-limit argument, but under an
`Algebra.IsInvariant` hypothesis that fails for the integral closure in `K̄`;
see AUDIT.md.

Taking it as data rather than deriving it makes the assumption explicit and
removes the vacuity that an unquantified `IsFrobAt v g → ...` would introduce.
Every result below that mentions `FrobeniusChoice` is conditional on it. -/
structure FrobeniusChoice where
  /-- The chosen element at each place. -/
  frob : HeightOneSpectrum A → AbsGal K Kbar
  /-- It is a Frobenius element there. -/
  isFrob : ∀ v, IsFrobAt A K Kbar v (frob v)

end FrobeniusChoice

section Compatibility

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)

/-- A representation is **unramified at `v`** if inertia acts trivially at
*every* prime above `v`.

Quantifying over all `Q` rather than one avoids having to prove transitivity of
the Galois action on primes above `v` before each use. The two readings agree
mathematically, since primes above `v` are conjugate and `ker ρ` is normal, but
that transitivity is not proved here; Mathlib v4.28.0's transitivity lemmas,
finite and profinite, both carry an invariance hypothesis that fails for the
integral closure in `K̄`.

If no prime of the integral closure lies over `v` this holds vacuously; that
primes do lie over `v` is true but is likewise not proved here. -/
def IsUnramifiedAt {lam : CoeffPlace E} (rho : LambdaAdicRep K Kbar E n lam)
    (v : HeightOneSpectrum A) : Prop :=
  ∀ Q : Ideal (IntClosure A Kbar), Q.IsPrime → Q.under A = v.asIdeal →
    ∀ g : AbsGal K Kbar, g ∈ Q.inertia (AbsGal K Kbar) → rho.toHom g = 1

/-- A **compatible family unramified outside `S`** with coefficients in the
completions `E_λ` themselves, relative to a chosen Frobenius at each place.

Evaluating at `Frob.frob v` rather than quantifying over all `g` with
`IsFrobAt v g` removes the vacuity: an implication `IsFrobAt v g → …` says
nothing if no Frobenius element is known to exist.

This is a legitimate notion, but it is not what the companion theorem
produces: Lafforgue's companions land in finite extensions of `E_λ`, not in
`E_λ`. See `exists_companion` and `CompanionRep`. -/
structure IsCompatibleFamily
    (Frob : FrobeniusChoice A K Kbar)
    (S : Finset (HeightOneSpectrum A))
    (rho : ∀ lam : CoeffPlace E, LambdaAdicRep K Kbar E n lam) : Prop where
  /-- Each `ρ_λ` is unramified at every `v ∉ S` with `v ∤ ℓ(λ)`. -/
  unramified : ∀ (lam : CoeffPlace E) (v : HeightOneSpectrum A),
    v ∉ S → NotDividing A E v lam → IsUnramifiedAt A K Kbar E n (rho lam) v
  /-- For `v ∉ S`, the characteristic polynomial of `ρ_λ(Frob_v)` is the image
  of a polynomial over `E` not depending on `λ`. -/
  charpoly : ∀ v : HeightOneSpectrum A, v ∉ S →
    ∃ P : E[X], ∀ lam : CoeffPlace E, NotDividing A E v lam →
      ((rho lam).toHom (Frob.frob v) :
          Matrix (Fin n) (Fin n) (Completion E lam)).charpoly
        = P.map (algebraMap E (Completion E lam))

/-- `ρ` has no invariant subspace over `E_λ` other than `⊥` and `⊤`.

Deliberately **not** the hypothesis of `exists_companion`. This is irreducibility
over `E_λ`, which is strictly weaker than absolute irreducibility; using it would
make the companion theorem stronger than Lafforgue's. `SpanFull` below is the
absolute notion, stated without any algebraic closure. Kept here to record the
distinction. -/
def IsIrred {lam : CoeffPlace E} (rho : LambdaAdicRep K Kbar E n lam) : Prop :=
  ∀ W : Submodule (Completion E lam) (Fin n → Completion E lam),
    (∀ g : AbsGal K Kbar, ∀ w ∈ W,
        (rho.toHom g : Matrix (Fin n) (Fin n) (Completion E lam)).mulVec w ∈ W) →
      W = ⊥ ∨ W = ⊤

end Compatibility

section AbsoluteConditions

/-- The image of `ρ` spans the full matrix algebra.

For `R` a field and `m ≥ 1` this is absolute irreducibility, stated with
no algebraic closure anywhere. The image contains `1` and is closed under
multiplication, so its `R`-linear span is already an `R`-subalgebra. If that
span is all of `M_m(R)` then it stays so
after any scalar extension, hence there is no proper nonzero invariant subspace
over any extension. Conversely, if `ρ` is absolutely irreducible then Burnside's
theorem over an algebraic closure `R̄` gives a span of dimension `m ^ 2`, and the
span over `R̄` is `R̄ ⊗ (span over R)`, so the span over `R` already has dimension
`m ^ 2`.

Both scope conditions hold at every use site: the coefficient rings are `E_λ`
and a finite extension `M` of it, and `exists_companion` assumes `0 < n`. Outside
that scope the reading degrades — at `m = 0` the predicate holds trivially while
irreducibility fails, and over a general `CommRing` the equivalence is not
well-posed. The definition is stated at `CommRing` generality because nothing
below needs more.

The equivalence is not formalised; it is what justifies the choice of predicate. -/
def SpanFull {G R : Type*} [Monoid G] [CommRing R] {m : ℕ}
    (rho : G →* GL (Fin m) R) : Prop :=
  Submodule.span R
      (Set.range fun g : G => (rho g : Matrix (Fin m) (Fin m) R)) = ⊤

/-- The determinant of `ρ` has finite order. The condition `0 < N` is essential:
`N = 0` would trivialise the predicate. -/
def DetFiniteOrderHom {G R : Type*} [Monoid G] [CommRing R] {m : ℕ}
    (rho : G →* GL (Fin m) R) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ g : G, ((rho g : Matrix (Fin m) (Fin m) R).det) ^ N = 1

end AbsoluteConditions

section CompanionRepDef

universe u

/-- A **companion representation** at `λ`: a continuous representation of `G_K`
into `GL_n(M)` for some finite extension `M` of `E_λ`, carrying the `E_λ`-module
topology. As with `AbsGal`, the structure asks of `Kbar` only that it extend
`K`; the `G_K` reading comes from the `IsAlgClosure` hypothesis in force where
the theorems use it.

The coefficient field is bundled because Lafforgue's theorem does not produce
companions over `E_λ` itself. Theorem VII.6(v) states the companion over a finite
extension of `E_λ`, and the obstruction to descending further for a fixed `E` is
the class of a central simple algebra, which Lafforgue's own proof works with.
Removing it by enlarging `E` is Chin's theorem, and is not formalised here.

The topology is pinned by `IsModuleTopology`, not left arbitrary: against an
arbitrary topology, `Continuous` would not assert the intended condition. -/
structure CompanionRep (K Kbar : Type*) [Field K] [Field Kbar] [Algebra K Kbar]
    (E : Type u) [Field E] [NumberField E] (n : ℕ) (lam : CoeffPlace E) where
  /-- The coefficient field, a finite extension of `E_λ`. -/
  M : Type u
  [instField : Field M]
  [instAlgebra : Algebra (Completion E lam) M]
  [instFiniteDimensional : FiniteDimensional (Completion E lam) M]
  [instTopologicalSpace : TopologicalSpace M]
  [instIsModuleTopology : IsModuleTopology (Completion E lam) M]
  /-- The representation. -/
  toHom : AbsGal K Kbar →* GL (Fin n) M
  continuous_toHom : Continuous toHom

attribute [instance] CompanionRep.instField CompanionRep.instAlgebra
  CompanionRep.instFiniteDimensional CompanionRep.instTopologicalSpace
  CompanionRep.instIsModuleTopology

end CompanionRepDef

section Companions

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)

/-- The finite-extension companion-existence consequence of Lafforgue's Theorem
VII.6, after fixing the coefficient field `E` and an `E_{λ₀}`-model, stated one
place `λ` at a time. Clause (v) gives the companion and its coefficient field;
the companion's finite-order determinant is carried from the construction in the
proof rather than read off the clause — and is in any case implied by the
unramifiedness and characteristic-polynomial conclusions together with `hdet`,
by the same Chebotarev density of the Frobenius classes and continuity of the
determinant.

This is a slice of VII.6, not the whole of it. VII.6 begins from an irreducible
lisse sheaf of finite-order determinant and constructs `E` and the polynomials
`P_v`; here both are supplied as data. VII.6 also proves purity, unit-ness of the Frobenius
roots away from `p` with slope bounds at the places over `p`, and a further
statement descending the `n`-fold direct sum of the
companion to `E_λ` itself, none of which is formalised.

`A` is a finite-type Dedekind `𝔽_q`-algebra with fraction field the function
field `K`, so `Spec A` is a smooth affine curve over `𝔽_q` and its closed points
are all but finitely many places of `K`. Without the finite-type hypothesis `A` could be a
discrete valuation ring or `K` itself and `HeightOneSpectrum A` a single point
or empty, collapsing the compatibility conditions. Finiteness of `K` over
`Fq(t)` is not assumed: the finite-type hypothesis and the compatible embedding
of `RatFunc Fq` already force it, which is why no `FunctionField` hypothesis
appears.

Hypotheses on `ρ₀`: absolute irreducibility (`SpanFull`), finite-order
determinant, unramified at every `v ∉ S`, and Frobenius characteristic
polynomials given by a fixed `P : v ↦ P v` over `E`. `P` is data rather than an
existential so that the same polynomials appear in the conclusion; this is what
ties the companion to `ρ₀`, and it is why no clause `rho lam₀ = rho₀` is needed
(that equality would
be type-inappropriate once the coefficient field varies).

Conclusion: a companion over a finite extension of `E_λ`, unramified outside `S`,
with the same `P v`, itself absolutely irreducible with finite-order determinant.

The curve here is the smooth affine `U = Spec A` with `S` removed, to which VII.6
applies after one change of convention: the Frobenius here is arithmetic,
`x ↦ x ^ #(A/v)`, where Lafforgue writes the characteristic polynomials for
geometric Frobenius, its inverse, and the polynomials of an invertible matrix
and of its inverse determine each other. The places of a proper model lying outside `Spec A` are
not points of `U`, so nothing is claimed about them. What is deliberately not
formalised is any descent of the coefficient field to `E_λ`.

Statement only: the proof is `sorry`. -/
theorem exists_companion
    {Fq : Type*} [Field Fq] [Finite Fq]
    [Algebra Fq A] [Algebra Fq K] [IsScalarTower Fq A K] [Algebra.FiniteType Fq A]
    [Algebra (RatFunc Fq) K] [IsScalarTower Fq (RatFunc Fq) K]
    (hn : 0 < n)
    (Frob : FrobeniusChoice A K Kbar)
    (S : Finset (HeightOneSpectrum A))
    (P : HeightOneSpectrum A → E[X])
    {lam₀ : CoeffPlace E} (hchar₀ : resChar E lam₀ ≠ ringChar K)
    (rho₀ : LambdaAdicRep K Kbar E n lam₀)
    (hspan : SpanFull rho₀.toHom)
    (hdet : DetFiniteOrderHom rho₀.toHom)
    (hunram : ∀ v : HeightOneSpectrum A, v ∉ S →
      IsUnramifiedAt A K Kbar E n rho₀ v)
    (hrat : ∀ v : HeightOneSpectrum A, v ∉ S →
      (rho₀.toHom (Frob.frob v) :
          Matrix (Fin n) (Fin n) (Completion E lam₀)).charpoly
        = (P v).map (algebraMap E (Completion E lam₀)))
    (lam : CoeffPlace E) (hchar : resChar E lam ≠ ringChar K) :
    ∃ rho : CompanionRep K Kbar E n lam,
      (∀ v : HeightOneSpectrum A, v ∉ S →
          ∀ Q : Ideal (IntClosure A Kbar), Q.IsPrime → Q.under A = v.asIdeal →
            ∀ g : AbsGal K Kbar, g ∈ Q.inertia (AbsGal K Kbar) →
              rho.toHom g = 1) ∧
      (∀ v : HeightOneSpectrum A, v ∉ S →
          (rho.toHom (Frob.frob v) : Matrix (Fin n) (Fin n) rho.M).charpoly
            = (P v).map ((algebraMap (Completion E lam) rho.M).comp
                (algebraMap E (Completion E lam)))) ∧
      SpanFull rho.toHom ∧ DetFiniteOrderHom rho.toHom := by
  sorry

end Companions

section CompanionFamily

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)

/-- The whole family of companions, one for each finite place of `E` away from
the characteristic, obtained from `exists_companion` by choice.

Same hypotheses as `exists_companion` with the target place removed. The choice
function assigns to each `λ` with `ℓ(λ) ≠ char K` a companion over its own finite
extension of `E_λ`, all of them matching the one family of polynomials `P`. This
is the Lean form of the statement that a family indexed by all `λ` follows from
the one-place-at-a-time version; it is proved, not assumed, but inherits the
`sorry` of `exists_companion`. -/
theorem exists_companion_family
    {Fq : Type*} [Field Fq] [Finite Fq]
    [Algebra Fq A] [Algebra Fq K] [IsScalarTower Fq A K] [Algebra.FiniteType Fq A]
    [Algebra (RatFunc Fq) K] [IsScalarTower Fq (RatFunc Fq) K]
    (hn : 0 < n)
    (Frob : FrobeniusChoice A K Kbar)
    (S : Finset (HeightOneSpectrum A))
    (P : HeightOneSpectrum A → E[X])
    {lam₀ : CoeffPlace E} (hchar₀ : resChar E lam₀ ≠ ringChar K)
    (rho₀ : LambdaAdicRep K Kbar E n lam₀)
    (hspan : SpanFull rho₀.toHom)
    (hdet : DetFiniteOrderHom rho₀.toHom)
    (hunram : ∀ v : HeightOneSpectrum A, v ∉ S →
      IsUnramifiedAt A K Kbar E n rho₀ v)
    (hrat : ∀ v : HeightOneSpectrum A, v ∉ S →
      (rho₀.toHom (Frob.frob v) :
          Matrix (Fin n) (Fin n) (Completion E lam₀)).charpoly
        = (P v).map (algebraMap E (Completion E lam₀))) :
    ∃ F : ∀ lam : CoeffPlace E, resChar E lam ≠ ringChar K →
        CompanionRep K Kbar E n lam,
      ∀ (lam : CoeffPlace E) (h : resChar E lam ≠ ringChar K),
        (∀ v : HeightOneSpectrum A, v ∉ S →
            ∀ Q : Ideal (IntClosure A Kbar), Q.IsPrime → Q.under A = v.asIdeal →
              ∀ g : AbsGal K Kbar, g ∈ Q.inertia (AbsGal K Kbar) →
                (F lam h).toHom g = 1) ∧
        (∀ v : HeightOneSpectrum A, v ∉ S →
            ((F lam h).toHom (Frob.frob v) :
                Matrix (Fin n) (Fin n) (F lam h).M).charpoly
              = (P v).map ((algebraMap (Completion E lam) (F lam h).M).comp
                  (algebraMap E (Completion E lam)))) ∧
        SpanFull (F lam h).toHom ∧ DetFiniteOrderHom (F lam h).toHom := by
  choose F hF using fun (lam : CoeffPlace E) (h : resChar E lam ≠ ringChar K) =>
    exists_companion (Fq := Fq) A K Kbar E n hn Frob S P hchar₀ rho₀ hspan
      hdet hunram hrat lam h
  exact ⟨F, hF⟩

end CompanionFamily

section FrobeniusIndependence

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)

omit [IsDedekindDomain A] [IsFractionRing A K] [IsAlgClosure K Kbar] in
/-- **Frobenius independence at a fixed prime.**

If `ρ` is unramified at `v` and `g`, `g'` are both Frobenius elements at the
same prime `Q` above `v`, then `ρ g = ρ g'`.

This is the correct well-definedness argument, and it runs through *inertia*,
not conjugacy: `IsArithFrobAt.mul_inv_mem_inertia` gives `g * g'⁻¹ ∈ inertia Q`,
which `ρ` kills. -/
theorem toHom_eq_of_isArithFrobAt {lam : CoeffPlace E}
    (rho : LambdaAdicRep K Kbar E n lam) {v : HeightOneSpectrum A}
    (hunram : IsUnramifiedAt A K Kbar E n rho v)
    {Q : Ideal (IntClosure A Kbar)} (hQp : Q.IsPrime) (hQu : Q.under A = v.asIdeal)
    {g g' : AbsGal K Kbar}
    (hg : IsArithFrobAt A g Q) (hg' : IsArithFrobAt A g' Q) :
    rho.toHom g = rho.toHom g' := by
  have hmem : g * g'⁻¹ ∈ Q.inertia (AbsGal K Kbar) := hg.mul_inv_mem_inertia hg'
  have h1 : rho.toHom (g * g'⁻¹) = 1 := hunram Q hQp hQu _ hmem
  rw [map_mul, map_inv] at h1
  exact mul_inv_eq_one.mp h1

omit [IsDedekindDomain A] [IsFractionRing A K] [IsAlgClosure K Kbar] in
/-- The characteristic polynomial of `ρ_λ(Frob_v)` is independent of the choice
of Frobenius element at a fixed prime above `v`. -/
theorem charpoly_eq_of_isArithFrobAt {lam : CoeffPlace E}
    (rho : LambdaAdicRep K Kbar E n lam) {v : HeightOneSpectrum A}
    (hunram : IsUnramifiedAt A K Kbar E n rho v)
    {Q : Ideal (IntClosure A Kbar)} (hQp : Q.IsPrime) (hQu : Q.under A = v.asIdeal)
    {g g' : AbsGal K Kbar}
    (hg : IsArithFrobAt A g Q) (hg' : IsArithFrobAt A g' Q) :
    (rho.toHom g : Matrix (Fin n) (Fin n) (Completion E lam)).charpoly
      = (rho.toHom g' : Matrix (Fin n) (Fin n) (Completion E lam)).charpoly := by
  rw [toHom_eq_of_isArithFrobAt A K Kbar E n rho hunram hQp hQu hg hg']

end FrobeniusIndependence

end LambdaAdicSlice
