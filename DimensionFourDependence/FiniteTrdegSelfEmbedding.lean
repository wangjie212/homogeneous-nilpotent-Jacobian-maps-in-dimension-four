import DimensionFourDependence.AlgebraicDerivation
import Mathlib.FieldTheory.FinTrdeg

/-! # Differential consequences of a dominant field self-embedding -/

namespace DimensionFourDependence

universe u

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- A field of finite transcendence degree is algebraic over the image
of every embedding into itself that fixes its coefficient field. -/
theorem finite_trdeg_self_embedding_isAlgebraic [FinTrdeg K F]
    (σ : F →ₐ[K] F) : Algebra.IsAlgebraic σ.fieldRange F := by
  have he := trdeg_add_eq (A := F) K σ.fieldRange
  have hr : Algebra.trdeg K σ.fieldRange = Algebra.trdeg K F :=
    σ.equivFieldRange.trdeg_eq.symm
  rw [hr] at he
  apply trdeg_eq_zero_iff.mp
  rcases Cardinal.add_eq_left_iff.mp he with h | h
  · exact False.elim ((not_le_of_gt (trdeg_lt_aleph0 K F))
      (le_trans (le_max_left _ _) h))
  · exact h

/-- In characteristic zero, a derivation vanishing on a dominant
self-embedding of a field of finite transcendence degree vanishes everywhere. -/
theorem derivation_zero_of_finite_trdeg_self_embedding [CharZero K] [FinTrdeg K F]
    (σ : F →ₐ[K] F) (D : Derivation K F F) (hD : ∀ z, D (σ z) = 0) : D = 0 := by
  letI : CharZero σ.fieldRange :=
    charZero_of_injective_algebraMap (algebraMap K σ.fieldRange).injective
  letI := finite_trdeg_self_embedding_isAlgebraic σ
  apply derivation_eq_zero_of_algebraic_base (E := σ.fieldRange) D
  · intro a
    obtain ⟨z, hz⟩ := a.property
    change D (a : F) = 0
    rw [← hz]
    exact hD z
  · intro z
    exact Algebra.IsAlgebraic.isAlgebraic z

end DimensionFourDependence
