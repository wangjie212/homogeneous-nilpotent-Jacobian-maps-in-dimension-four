import DimensionFourDependence.ConstantField

/-! # Extending coordinate derivations through algebraic field extensions

These are the existence, uniqueness, and mixed-partial compatibility inputs
used when passing from `K(Y)` to the algebraic coefficient field in Lemma 2.2.
Existence in this module is for finite extensions. Uniqueness and commutation
use only algebraicity. `AlgebraicDifferential.lean` glues the finite
constructions and removes the finiteness restriction for the coefficient field.
-/

namespace DimensionFourDependence

variable {K E L : Type*} [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]

/-- A derivation killing a larger base field is linear over that field. -/
noncomputable def derivationChangeBase (D : Derivation K L L)
    (hE : ∀ a : E, D (algebraMap E L a) = 0) : Derivation E L L where
  toLinearMap :=
    { toFun := D
      map_add' := map_add D
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [D.leibniz, hE, smul_zero, add_zero]
        rfl }
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

theorem derivationChangeBase_apply (D : Derivation K L L)
    (hE : ∀ a : E, D (algebraMap E L a) = 0) (x : L) :
    derivationChangeBase D hE x = D x := rfl

/-- Vanishing on the base forces vanishing on an algebraic extension in
characteristic zero. -/
theorem derivation_eq_zero_of_algebraic_base [CharZero E]
    (D : Derivation K L L) (hE : ∀ a : E, D (algebraMap E L a) = 0)
    (hAlg : ∀ x : L, IsAlgebraic E x) : D = 0 := by
  ext x
  exact derivation_zero_of_isAlgebraic (derivationChangeBase D hE) x (hAlg x)

/-- Two extensions of the same derivation agree on every algebraic element. -/
theorem derivation_extension_unique [CharZero E]
    (D₁ D₂ : Derivation K L L)
    (hE : ∀ a : E, D₁ (algebraMap E L a) = D₂ (algebraMap E L a))
    (hAlg : ∀ x : L, IsAlgebraic E x) : D₁ = D₂ := by
  have hzero : D₁ - D₂ = 0 := derivation_eq_zero_of_algebraic_base _
    (fun a => by simp only [Derivation.sub_apply, hE, sub_self]) hAlg
  exact sub_eq_zero.mp hzero

/-- Convert an integer derivation into a `K`-derivation once it kills `K`. -/
noncomputable def intDerivationToBase (D : Derivation ℤ L L)
    (hK : ∀ a : K, D (algebraMap K L a) = 0) : Derivation K L L where
  toLinearMap :=
    { toFun := D
      map_add' := map_add D
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [D.leibniz, hK, smul_zero, add_zero]
        rfl }
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

theorem intDerivationToBase_apply (D : Derivation ℤ L L)
    (hK : ∀ a : K, D (algebraMap K L a) = 0) (x : L) :
    intDerivationToBase D hK x = D x := rfl

/-- Every `K`-derivation on a characteristic-zero field extends uniquely
through a finite field extension. Existence uses Mathlib's construction
via a primitive element and its separable minimal polynomial. -/
theorem existsUnique_derivation_extension_finite [CharZero K] [FiniteDimensional E L]
    (D : Derivation K E E) :
    ∃! Δ : Derivation K L L,
      ∀ a : E, Δ (algebraMap E L a) = algebraMap E L (D a) := by
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  letI : Differential E := ⟨D.restrictScalars ℤ⟩
  letI : Differential L := Differential.differentialFiniteDimensional E L
  letI : DifferentialAlgebra E L := Differential.differentialAlgebraFiniteDimensional
  have hK : ∀ a : K, Differential.deriv (algebraMap K L a) = 0 := by
    intro a
    rw [IsScalarTower.algebraMap_apply K E L, deriv_algebraMap]
    change algebraMap E L (D (algebraMap K E a)) = 0
    rw [D.map_algebraMap, map_zero]
  let Δ := intDerivationToBase Differential.deriv hK
  have hΔ : ∀ a : E, Δ (algebraMap E L a) = algebraMap E L (D a) := by
    intro a
    exact deriv_algebraMap a
  refine ⟨Δ, hΔ, ?_⟩
  intro Δ' hΔ'
  apply derivation_extension_unique (K := K) (E := E) Δ' Δ
  · intro a
    rw [hΔ', hΔ]
  · intro x
    exact IsAlgebraic.of_finite E x

/-- Commuting derivations on the base remain commuting on an algebraic
extension. This supplies symmetry of mixed coordinate derivatives. -/
theorem derivation_extensions_commute [CharZero E]
    (d₁ d₂ : Derivation K E E) (D₁ D₂ : Derivation K L L)
    (h₁ : ∀ a : E, D₁ (algebraMap E L a) = algebraMap E L (d₁ a))
    (h₂ : ∀ a : E, D₂ (algebraMap E L a) = algebraMap E L (d₂ a))
    (hcomm : ∀ a : E, d₁ (d₂ a) = d₂ (d₁ a))
    (hAlg : ∀ x : L, IsAlgebraic E x) (x : L) : D₁ (D₂ x) = D₂ (D₁ x) := by
  have hzero : ⁅D₁, D₂⁆ = 0 := by
    apply derivation_eq_zero_of_algebraic_base _ _ hAlg
    intro a
    simp only [Derivation.commutator_apply, h₁, h₂, hcomm, sub_self]
  have h := congrArg (fun D : Derivation K L L => D x) hzero
  simpa only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] using h

end DimensionFourDependence
