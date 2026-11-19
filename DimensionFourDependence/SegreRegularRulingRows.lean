import DimensionFourDependence.SegreRulingLocalJacobianReduction

/-! # Ruling preservation constructs the regular slope and exact output rows -/

namespace DimensionFourDependence

set_option maxHeartbeats 3000000

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- Agreement of the actual output row ratio with the source ruling
parameter in the uniformizer residue constructs its regular first-order
correction. No correction coefficient or divided difference is supplied. -/
theorem segre_ruling_residue_agreement_constructs_regular_slope
    (π t v : O) (u : Oˣ)
    (hmax : IsLocalRing.maximalIdeal O = Ideal.span {π})
    (hpres : IsLocalRing.residue O (v * (↑u⁻¹ : O)) = IsLocalRing.residue O t) :
    ∃ a : O, v = (t + π * a) * (u : O) := by
  have hzero : IsLocalRing.residue O (v * (↑u⁻¹ : O) - t) = 0 := by
    rw [map_sub, hpres, sub_self]
  have hmem : v * (↑u⁻¹ : O) - t ∈ Ideal.span {π} := by
    rw [← hmax]
    exact (IsLocalRing.residue_eq_zero_iff _).mp hzero
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hmem
  have hratio : v * (↑u⁻¹ : O) = t + π * a := by linear_combination ha
  refine ⟨a, ?_⟩
  calc
    v = (v * (↑u⁻¹ : O)) * (u : O) := by simp [mul_assoc]
    _ = (t + π * a) * (u : O) := congrArg (fun z => z * (u : O)) hratio

/-- An exact normalized determinant relation and preservation of the
specified ruling in the residue construct the complete proportional
output-row formula in the same local ring. -/
theorem segre_regular_normalized_rows_construct_ruling_formula
    (j : ℕ) (π t : O) (p : Fin 4 → O) (u : Oˣ) (hfirst : p 0 = (u : O))
    (hmax : IsLocalRing.maximalIdeal O = Ideal.span {π})
    (hpres : IsLocalRing.residue O (p 2 * (↑u⁻¹ : O)) = IsLocalRing.residue O t)
    (hdet : p 0 * p 3 - p 1 * p 2 = 0) :
    ∃ a : O, (fun i => π ^ j * p i) = segreRulingLocalOutputRows j π t a (p 0) (p 1) := by
  obtain ⟨a, ha⟩ := segre_ruling_residue_agreement_constructs_regular_slope π t (p 2) u hmax hpres
  have hp2 : p 2 = (t + π * a) * p 0 := by simpa only [hfirst] using ha
  have hp3 : p 3 = (t + π * a) * p 1 := by
    have hunit : IsUnit (p 0) := by rw [hfirst]; exact u.isUnit
    apply hunit.mul_left_cancel
    rw [hp2] at hdet
    linear_combination hdet
  refine ⟨a, ?_⟩
  funext i
  fin_cases i <;> simp [segreRulingLocalOutputRows, hp2, hp3] <;> ring

/-- The original determinant identity descends through the same common
uniformizer power to the normalized rows, and ruling preservation then
constructs the regular slope and all four exact original local outputs. -/
theorem segre_regular_factored_outputs_construct_ruling_formula
    [IsDomain O] (j : ℕ) (π t : O) (hπ : π ≠ 0)
    (h p : Fin 4 → O) (hfactor : ∀ i, h i = π ^ j * p i)
    (u : Oˣ) (hfirst : p 0 = (u : O))
    (hmax : IsLocalRing.maximalIdeal O = Ideal.span {π})
    (hpres : IsLocalRing.residue O (p 2 * (↑u⁻¹ : O)) = IsLocalRing.residue O t)
    (hdet : h 0 * h 3 - h 1 * h 2 = 0) :
    ∃ a : O, h = segreRulingLocalOutputRows j π t a (p 0) (p 1) := by
  have hpdet : p 0 * p 3 - p 1 * p 2 = 0 := by
    have he : (π ^ j) ^ 2 * (p 0 * p 3 - p 1 * p 2) = 0 := by
      simp only [hfactor] at hdet
      linear_combination hdet
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (pow_ne_zero j hπ))
  obtain ⟨a, ha⟩ := segre_regular_normalized_rows_construct_ruling_formula j π t p u hfirst hmax hpres hpdet
  refine ⟨a, ?_⟩
  exact (funext hfactor).trans ha

end DimensionFourDependence
