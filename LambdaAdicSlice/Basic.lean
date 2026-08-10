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

section MissingFromMathlib

/-!
## Ingredients not available in Mathlib v4.28.0

* `Frob_v` in the *absolute* Galois group. `Mathlib/RingTheory/Frobenius.lean`
  provides `arithFrobAt` only for a finite group acting on a ring, i.e. at
  finite level; there is no inverse-limit construction, and no
  conjugacy-class-valued Frobenius for `G_K`.
* The unramified-outside-`S` condition *for a representation*.
* The condition `v ∤ ℓ(λ)` relating a place of `K` to the residue
  characteristic of a place of `E`.

Each is taken as a parameter below.
-/

variable (A K : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
variable (Kbar : Type*) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)

-- `IsFrobAt v g` : `g` is a Frobenius element at the place `v`.
variable (IsFrobAt : HeightOneSpectrum A → AbsGal K Kbar → Prop)

-- `IsUnramAt lam ρ v` : the representation `ρ` is unramified at `v`.
variable (IsUnramAt : ∀ lam : CoeffPlace E,
  LambdaAdicRep K Kbar E n lam → HeightOneSpectrum A → Prop)

-- `Good v lam` : `v ∤ ℓ(λ)`, i.e. `v` does not divide the residue
-- characteristic of `lam`.
variable (Good : HeightOneSpectrum A → CoeffPlace E → Prop)

end MissingFromMathlib

section CompatibleFamily

variable (A K : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
variable (Kbar : Type*) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)
variable (IsFrobAt : HeightOneSpectrum A → AbsGal K Kbar → Prop)
variable (IsUnramAt : ∀ lam : CoeffPlace E,
  LambdaAdicRep K Kbar E n lam → HeightOneSpectrum A → Prop)
variable (Good : HeightOneSpectrum A → CoeffPlace E → Prop)

/-- A family `(ρ_λ)` of `λ`-adic representations is a **compatible family
unramified outside `S`**.

The `charpoly` field states both halves of condition (2) at once: the
polynomial `P` is quantified *outside* `λ`, so it simultaneously says the
characteristic polynomial has coefficients in `E` and is independent of `λ`. -/
structure IsCompatibleFamily
    (S : Finset (HeightOneSpectrum A))
    (rho : ∀ lam : CoeffPlace E, LambdaAdicRep K Kbar E n lam) : Prop where
  /-- Each `ρ_λ` is unramified at every `v ∉ S` with `v ∤ ℓ(λ)`. -/
  unramified : ∀ (lam : CoeffPlace E) (v : HeightOneSpectrum A),
    v ∉ S → Good v lam → IsUnramAt lam (rho lam) v
  /-- For `v ∉ S`, the characteristic polynomial of `ρ_λ(Frob_v)` is the image
  of a polynomial over `E` not depending on `λ`. -/
  charpoly : ∀ v : HeightOneSpectrum A, v ∉ S →
    ∃ P : E[X], ∀ (lam : CoeffPlace E) (g : AbsGal K Kbar),
      Good v lam → IsFrobAt v g →
        ((rho lam).toHom g : Matrix (Fin n) (Fin n) (Completion E lam)).charpoly
          = P.map (algebraMap E (Completion E lam))

end CompatibleFamily

end LambdaAdicSlice

namespace LambdaAdicSlice

section Lafforgue

variable (A K : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
variable (Kbar : Type*) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)
variable (IsFrobAt : HeightOneSpectrum A → AbsGal K Kbar → Prop)
variable (IsUnramAt : ∀ lam : CoeffPlace E,
  LambdaAdicRep K Kbar E n lam → HeightOneSpectrum A → Prop)
variable (Good : HeightOneSpectrum A → CoeffPlace E → Prop)

-- `K` is a global function field: the function field of a smooth projective
-- curve over the finite field `Fq`. Mathlib's `FunctionField Fq K` gives the
-- field-theoretic half; there is no curve attached to it in v4.28.0.
variable (Fq : Type*) [Field Fq] [Finite Fq] [Algebra (RatFunc Fq) K]

/-- **Deligne's conjecture for curves** (L. Lafforgue).

Every continuous `λ`-adic representation of `G_K` unramified outside `S` is a
member of a compatible family unramified outside `S`.

Statement only: the proof is `sorry`. -/
theorem exists_isCompatibleFamily_of_unramified
    (hK : FunctionField Fq K)
    (S : Finset (HeightOneSpectrum A))
    (lam₀ : CoeffPlace E)
    (hchar : ringChar (𝓞 E ⧸ lam₀.asIdeal) ≠ ringChar K)
    (rho₀ : LambdaAdicRep K Kbar E n lam₀)
    (hunram : ∀ v : HeightOneSpectrum A, v ∉ S → IsUnramAt lam₀ rho₀ v) :
    ∃ rho : ∀ lam : CoeffPlace E, LambdaAdicRep K Kbar E n lam,
      rho lam₀ = rho₀ ∧
        IsCompatibleFamily A K Kbar E n IsFrobAt IsUnramAt Good S rho := by
  sorry

end Lafforgue

end LambdaAdicSlice

namespace LambdaAdicSlice

section FrobeniusSystem

variable (A K : Type*) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]
variable (Kbar : Type*) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
variable (E : Type*) [Field E] [NumberField E] (n : ℕ)

/-- Characterising axioms for an abstract Frobenius predicate on `G_K`.

Mathlib v4.28.0 cannot construct `Frob_v` in the absolute Galois group. The
predicate `IsArithFrobAt` is available for a *monoid* acting on a ring — no
finiteness required — but the action of `G_K` on the integral closure of `A`
in `K̄` is not instantiated, so the predicate cannot be applied at that level.

These are the properties the compatible-family definition actually depends on:
a Frobenius exists at each place, and it is well defined up to conjugacy. -/
structure IsFrobeniusSystem
    (IsFrobAt : HeightOneSpectrum A → AbsGal K Kbar → Prop) : Prop where
  /-- A Frobenius element exists at every finite place. -/
  exists_frob : ∀ v : HeightOneSpectrum A, ∃ g, IsFrobAt v g
  /-- Any two Frobenius elements at the same place are conjugate. -/
  isConj_of : ∀ (v : HeightOneSpectrum A) (g g' : AbsGal K Kbar),
    IsFrobAt v g → IsFrobAt v g' → IsConj g g'
  /-- Frobenius elements at a place are closed under conjugation. -/
  conj_mem : ∀ (v : HeightOneSpectrum A) (g x : AbsGal K Kbar),
    IsFrobAt v g → IsFrobAt v (x * g * x⁻¹)

end FrobeniusSystem

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
