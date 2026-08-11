/-
Statement-level formalisation: compatible families of λ-adic representations
and the char-poly independence condition.

Every proof is `sorry`. Ingredients Mathlib v4.28.0 cannot construct are taken
as explicit parameters and documented as such.
-/
import Mathlib

open IsDedekindDomain NumberField Matrix Polynomial

namespace LambdaAdicSlice

section Setup

-- `A` is a Dedekind domain with fraction field `K`; the finite places of `K`
-- are the height-one primes of `A`. This covers number fields (`A = 𝓞 K`) and
-- function fields of curves over finite fields alike.
variable (A K : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]

-- A fixed algebraic closure of `K`.
variable (Kbar : Type*) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]

/-- The absolute Galois group `G_K`. The Krull topology instance comes from
`Mathlib/FieldTheory/KrullTopology.lean`. -/
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



end LambdaAdicSlice

namespace LambdaAdicSlice


end LambdaAdicSlice

namespace LambdaAdicSlice


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
/-- The characteristic polynomial of `ρ_λ(Frob_v)` does not depend on the
choice of Frobenius element at `v`.

This is the well-definedness fact that makes the compatible-family condition
meaningful. It is proved from `IsFrobeniusSystem.isConj_of`. -/
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

end LambdaAdicSlice

namespace LambdaAdicSlice

section FrobeniusConcrete

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]

/-- The integral closure of `A` in `K̄`. -/
abbrev IntClosure := integralClosure A Kbar

/-- `G_K` acts on the integral closure of `A` in `K̄`.

This instance is **not** in Mathlib v4.28.0 and is the missing link that
prevents `IsArithFrobAt` from being applied to the absolute Galois group. -/
instance : MulSemiringAction (AbsGal K Kbar) (IntClosure A Kbar) where
  smul g x := ⟨g x, IsIntegral.map ((g : Kbar →ₐ[K] Kbar).restrictScalars A) x.2⟩
  one_smul x := by ext; simp
  mul_smul g h x := by ext; simp
  smul_zero g := by ext; simp
  smul_add g x y := by ext; simp
  smul_one g := by ext; simp
  smul_mul g x y := by ext; simp

end FrobeniusConcrete

end LambdaAdicSlice

namespace LambdaAdicSlice

section FrobeniusDefined

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]

/-- The `G_K`-action commutes with the `A`-action, because `A` lands in `K`
and `G_K` fixes `K` pointwise. Required by `IsArithFrobAt`. -/
instance : SMulCommClass (AbsGal K Kbar) A (IntClosure A Kbar) where
  smul_comm g a x := by
    ext
    simp [Algebra.smul_def, IsScalarTower.algebraMap_apply A K Kbar]

/-- `g : G_K` is a **Frobenius at `v`** if there is a prime `Q` of the integral
closure of `A` in `K̄` lying over `v` at which `g` is an arithmetic Frobenius in
Mathlib's sense (`IsArithFrobAt`).

This is a definition, not an axiom: it uses `Mathlib/RingTheory/Frobenius.lean`
directly, via the `MulSemiringAction` instance above. -/
def IsFrobAt (v : HeightOneSpectrum A) (g : AbsGal K Kbar) : Prop :=
  ∃ Q : Ideal (IntClosure A Kbar), Q.IsPrime ∧ Q.under A = v.asIdeal ∧
    IsArithFrobAt A g Q

end FrobeniusDefined

end LambdaAdicSlice

namespace LambdaAdicSlice

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

end LambdaAdicSlice

namespace LambdaAdicSlice

section ConcreteConditions

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)

/-- The residue characteristic `ℓ(λ)` of a finite place of `E`. -/
noncomputable def resChar (lam : CoeffPlace E) : ℕ := ringChar (𝓞 E ⧸ lam.asIdeal)

/-- `v ∤ ℓ(λ)`: the residue characteristic of `λ` is not in the prime `v`.

A definition, replacing the earlier `Good` parameter. -/
def NotDividing (v : HeightOneSpectrum A) (lam : CoeffPlace E) : Prop :=
  ((resChar E lam : ℕ) : A) ∉ v.asIdeal

end ConcreteConditions

end LambdaAdicSlice

namespace LambdaAdicSlice


end LambdaAdicSlice

namespace LambdaAdicSlice


end LambdaAdicSlice

namespace LambdaAdicSlice


end LambdaAdicSlice

namespace LambdaAdicSlice

section FrobeniusChoice

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]

/-- A choice of Frobenius element at every finite place.

Existence of Frobenius elements in the *absolute* Galois group is not available
in Mathlib v4.28.0: `IsArithFrobAt.exists_of_isInvariant` requires a finite
residue field at the chosen prime, which fails at `K̄`. Proving it needs the
surjectivity of the decomposition group onto the residue Galois group together
with an inverse-limit or Zorn argument over finite subextensions.

Taking it as data rather than deriving it makes the assumption explicit and
removes the vacuity that an unquantified `IsFrobAt v g → ...` would introduce. -/
structure FrobeniusChoice where
  /-- The chosen element at each place. -/
  frob : HeightOneSpectrum A → AbsGal K Kbar
  /-- It is a Frobenius element there. -/
  isFrob : ∀ v, IsFrobAt A K Kbar v (frob v)

end FrobeniusChoice

end LambdaAdicSlice

namespace LambdaAdicSlice

section VacuityFree

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)

/-- A representation is **unramified at `v`** if inertia acts trivially at
*every* prime above `v`.

Quantifying over all `Q` rather than one avoids having to prove transitivity of
the Galois action on primes above `v` before each use. The two readings agree
mathematically, since primes above `v` are conjugate and `ker ρ` is normal. -/
def IsUnramifiedAt {lam : CoeffPlace E} (rho : LambdaAdicRep K Kbar E n lam)
    (v : HeightOneSpectrum A) : Prop :=
  ∀ Q : Ideal (IntClosure A Kbar), Q.IsPrime → Q.under A = v.asIdeal →
    ∀ g : AbsGal K Kbar, g ∈ Q.inertia (AbsGal K Kbar) → rho.toHom g = 1

/-- A **compatible family unramified outside `S`**, relative to a chosen
Frobenius at each place.

Evaluating at `Frob.frob v` rather than quantifying over all `g` with
`IsFrobAt v g` removes the vacuity: an implication `IsFrobAt v g → …` says
nothing if no Frobenius element is known to exist. -/
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

end VacuityFree

end LambdaAdicSlice

namespace LambdaAdicSlice

section LafforgueHypotheses

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)

/-- The determinant of `ρ` has finite order. -/
def DetFiniteOrder {lam : CoeffPlace E} (rho : LambdaAdicRep K Kbar E n lam) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ g : AbsGal K Kbar,
    ((rho.toHom g : Matrix (Fin n) (Fin n) (Completion E lam)).det) ^ N = 1

/-- `ρ` has no invariant subspace other than `⊥` and `⊤`.

This is irreducibility over `E_λ`. The hypothesis in Lafforgue's theorem is
*absolute* irreducibility, i.e. irreducibility after base change to an algebraic
closure of `E_λ`; that base change is not formalised here. -/
def IsIrred {lam : CoeffPlace E} (rho : LambdaAdicRep K Kbar E n lam) : Prop :=
  ∀ W : Submodule (Completion E lam) (Fin n → Completion E lam),
    (∀ g : AbsGal K Kbar, ∀ w ∈ W,
        (rho.toHom g : Matrix (Fin n) (Fin n) (Completion E lam)).mulVec w ∈ W) →
      W = ⊥ ∨ W = ⊤

/-- The Frobenius characteristic polynomials of `ρ` at places outside `S` have
coefficients in `E`.

Without this the conclusion of the companion theorem cannot hold: an unramified
rank-one character of the constant-field quotient can have Frobenius eigenvalues
outside `E`. -/
def FrobCharpolyRational {lam : CoeffPlace E} (Frob : FrobeniusChoice A K Kbar)
    (S : Finset (HeightOneSpectrum A)) (rho : LambdaAdicRep K Kbar E n lam) : Prop :=
  ∀ v : HeightOneSpectrum A, v ∉ S → ∃ P : E[X],
    ((rho.toHom (Frob.frob v) : Matrix (Fin n) (Fin n) (Completion E lam)).charpoly)
      = P.map (algebraMap E (Completion E lam))

end LafforgueHypotheses

section LafforgueCorrected

variable (A K Kbar : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
  [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  [Algebra A Kbar] [IsScalarTower A K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)
variable (Fq : Type*) [Field Fq] [Finite Fq] [Algebra (RatFunc Fq) K]

/-- **Lafforgue's companion theorem**, with the hypotheses required for the
statement to be true.

An earlier version of this file stated the conclusion for *every* continuous
representation unramified outside `S`. That is false: a rank-one unramified
character of the constant-field quotient can have Frobenius eigenvalues outside
`E`. Irreducibility, finite-order determinant, and `E`-rationality of the
Frobenius characteristic polynomials are all needed.

Known gaps, deliberately not formalised: absolute irreducibility (`IsIrred` is
irreducibility over `E_λ`); the coefficient-field descent, so that the companions
land in `E_λ` rather than in finite extensions of it (this is Chin's theorem, not
Lafforgue's); and `HeightOneSpectrum A` indexes the closed points of an affine
model, omitting the places at infinity of the projective curve.

Statement only: the proof is `sorry`. -/
theorem exists_isCompatibleFamily''_of_irreducible
    (hK : FunctionField Fq K)
    (hn : 0 < n)
    (Frob : FrobeniusChoice A K Kbar)
    (S : Finset (HeightOneSpectrum A))
    (lam₀ : CoeffPlace E)
    (hchar : resChar E lam₀ ≠ ringChar K)
    (rho₀ : LambdaAdicRep K Kbar E n lam₀)
    (hirred : IsIrred K Kbar E n rho₀)
    (hdet : DetFiniteOrder K Kbar E n rho₀)
    (hunram : ∀ v : HeightOneSpectrum A, v ∉ S →
      IsUnramifiedAt A K Kbar E n rho₀ v)
    (hrat : FrobCharpolyRational A K Kbar E n Frob S rho₀) :
    ∃ rho : ∀ lam : CoeffPlace E, LambdaAdicRep K Kbar E n lam,
      rho lam₀ = rho₀ ∧ IsCompatibleFamily A K Kbar E n Frob S rho := by
  sorry

end LafforgueCorrected

end LambdaAdicSlice

namespace LambdaAdicSlice

section InertiaCorrect

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
which `ρ` kills. An earlier version of this file asserted instead that any two
Frobenius elements at a place are conjugate — that is false. -/
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

end InertiaCorrect

end LambdaAdicSlice
