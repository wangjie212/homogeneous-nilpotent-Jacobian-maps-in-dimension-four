import DimensionFourDependence.RationalJacobianCriterion

/-! # The common constants of the extended output partials over a closed field -/

namespace DimensionFourDependence

open MvPolynomial Algebra

universe u

set_option maxHeartbeats 1500000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K] {n m : ℕ}
local notation "F" => FractionRing (MvPolynomial (Fin n) K)

/-- Vanishing of every actual rational source partial forces the
element to lie in the original algebraically closed ground field. -/
theorem closed_field_all_rational_partials_zero_is_scalar
    (a : F) (h : ∀ j : Fin n, rationalPartial (K := K) j a = 0) :
    ∃ c : K, algebraMap K F c = a := by
  let Y : Fin 1 → F := fun _ => a
  have hJ : rationalJacobian Y = 0 := by
    funext i j
    exact h j
  let E := IntermediateField.adjoin K (Set.range Y)
  have he : Algebra.trdeg K E = 0 := by
    change Algebra.trdeg K (IntermediateField.adjoin K (Set.range Y)) = 0
    rw [rationalJacobian_rank_eq_output_trdeg Y, hJ, Matrix.rank_zero, Nat.cast_zero]
  let : Algebra.IsAlgebraic K E := trdeg_eq_zero_iff.mp he
  let b : E := ⟨a, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := E)).2 b
  exact ⟨c, congrArg (fun z : E => (z : F)) hc⟩

omit [IsAlgClosed K] in
theorem coefficientPartial_killed_by_all_computes_original_source_partials_zero
    (Y : Fin m → F) (hY : AlgebraicIndependent K Y) (a : coefficientField (K := K) Y)
    (h : ∀ i, coefficientPartial Y hY i a = 0) :
    ∀ j : Fin n, rationalPartial (K := K) j (a : F) = 0 := by
  intro j
  rw [coefficient_chain_rule Y hY]
  simp [h]

/-- The extended output partials have common constants exactly in K. -/
theorem closed_field_coefficientPartials_common_constant_is_scalar
    (Y : Fin m → F) (hY : AlgebraicIndependent K Y) (a : coefficientField (K := K) Y)
    (h : ∀ i, coefficientPartial Y hY i a = 0) :
    ∃ c : K, algebraMap K (coefficientField (K := K) Y) c = a := by
  obtain ⟨c, hc⟩ := closed_field_all_rational_partials_zero_is_scalar (a : F)
    (coefficientPartial_killed_by_all_computes_original_source_partials_zero Y hY a h)
  exact ⟨c, Subtype.ext hc⟩

end DimensionFourDependence
