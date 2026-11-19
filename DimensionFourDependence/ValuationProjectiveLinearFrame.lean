import DimensionFourDependence.ValuativeIntegralCriterion

/-! # A linear frame selects an original projective chart in every valuation ring

If all coordinates divided by a nonzero linear frame are regular in a
valuation ring, their original linear combination is one. Some original
coordinate is therefore a unit, and all ratios in its original chart are
regular. No projective coordinate change or new chart cover is assumed.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- In a nonzero linear frame, some original projective coordinate is
a unit in every valuation ring containing the original coefficients and
all frame ratios. -/
theorem valuation_linear_frame_exists_unit_coordinate
    (x : Fin 4 → L) (c : Fin 4 → k) (h : L) (hh : h ≠ 0)
    (hlinear : h = ∑ i, algebraMap k L (c i) * x i)
    (V : ValuationSubring L) (hk : ∀ a : k, algebraMap k L a ∈ V)
    (hx : ∀ i, x i / h ∈ V) :
    ∃ j : Fin 4, IsUnit (⟨x j / h, hx j⟩ : V) := by
  classical
  let a : Fin 4 → V := fun i => ⟨algebraMap k L (c i), hk (c i)⟩
  let y : Fin 4 → V := fun i => ⟨x i / h, hx i⟩
  have hsum : (∑ i, a i * y i) = 1 := by
    apply Subtype.val_injective
    change V.subtype (∑ i, a i * y i) = V.subtype 1
    simp only [map_sum, map_mul, map_one]
    change (∑ i, algebraMap k L (c i) * (x i / h)) = 1
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, ← hlinear, div_self hh]
  change ∃ j, IsUnit (y j)
  by_contra! hnot
  have hmax (i : Fin 4) : y i ∈ IsLocalRing.maximalIdeal V :=
    (IsLocalRing.mem_maximalIdeal _).mpr (hnot i)
  have hbad : (∑ i, a i * y i) ∈ IsLocalRing.maximalIdeal V :=
    Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (hmax i))
  rw [hsum] at hbad
  exact (Ideal.IsMaximal.ne_top inferInstance)
    ((IsLocalRing.maximalIdeal V).eq_top_of_isUnit_mem hbad isUnit_one)

/-- The unit original coordinate supplies its original projective
chart, with every actual coordinate ratio regular in the given valuation
ring. This uses the original chart rather than an auxiliary linear one. -/
theorem valuation_linear_frame_exists_original_chart
    (x : Fin 4 → L) (c : Fin 4 → k) (h : L) (hh : h ≠ 0)
    (hlinear : h = ∑ i, algebraMap k L (c i) * x i)
    (V : ValuationSubring L) (hk : ∀ a : k, algebraMap k L a ∈ V)
    (hx : ∀ i, x i / h ∈ V) :
    ∃ j : Fin 4, IsUnit (⟨x j / h, hx j⟩ : V) ∧ ∀ i, x i / x j ∈ V := by
  obtain ⟨j, hj⟩ := valuation_linear_frame_exists_unit_coordinate x c h hh hlinear V hk hx
  refine ⟨j, hj, ?_⟩
  intro i
  have hinv : (x j / h)⁻¹ ∈ V := Submonoid.inv_mem_of_isUnit hj
  have hratio := V.mul_mem _ _ (hx i) hinv
  simpa only [← div_eq_mul_inv, div_div_div_cancel_right₀ hh] using hratio

end DimensionFourDependence
