import DimensionFourDependence.AlgebraicDerivation

/-! # A nonzero derivation cannot annihilate a full transcendence basis -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

/-- An independent family of the full ambient transcendence degree
would make the ambient field algebraic over constants, contradicting
the nonzero original derivation. -/
theorem nonzero_derivation_full_dimension_constants_not_algebraicIndependent
    (D : Derivation K F F) (hD : D ≠ 0) (htr : Algebra.trdeg K F ≤ n)
    (Y : Fin n → F) (hDY : ∀ i, D (Y i) = 0) : ¬AlgebraicIndependent K Y := by
  intro hY
  have hb := hY.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by simpa using htr)
  let E := IntermediateField.adjoin K (Set.range Y)
  have hE : E ≤ derivationConstants D := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro y ⟨i, rfl⟩
    exact hDY i
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  apply hD
  ext z
  exact derivation_zero_of_isAlgebraic (derivationOverConstantSubfield D E hE) z
    (IntermediateField.isAlgebraic_adjoin_iff.mpr (hb.isAlgebraic.isAlgebraic z))

/-- The derivation constructs an actual nonzero polynomial relation
among any full-size family of its constants. -/
theorem nonzero_derivation_constructs_relation_among_full_dimension_constants
    (D : Derivation K F F) (hD : D ≠ 0) (htr : Algebra.trdeg K F ≤ n)
    (Y : Fin n → F) (hDY : ∀ i, D (Y i) = 0) :
    ∃ R : MvPolynomial (Fin n) K, R ≠ 0 ∧ aeval Y R = 0 := by
  have hnot := nonzero_derivation_full_dimension_constants_not_algebraicIndependent D hD htr Y hDY
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero] at hnot
  push Not at hnot
  obtain ⟨R, hzero, hR⟩ := hnot
  exact ⟨R, hR, hzero⟩

end DimensionFourDependence
