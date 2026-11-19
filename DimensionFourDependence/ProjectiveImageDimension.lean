import DimensionFourDependence.ProjectiveOutputField
import DimensionFourDependence.ProjectiveEulerWeight
import DimensionFourDependence.OutputCoordinateFieldEquiv

/-! # The actual rank-three projective image has function-field dimension two

Positive homogeneous Euler weight separates one affine output from all
actual projective ratios. The affine output field has dimension three
by the Jacobian criterion, so the projective ratio field has dimension
two. The checked chart-coordinate fraction-field equivalence identifies
this with the actual prime quotient's function field.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The actual affine output field of any positive homogeneous map
has one more transcendence degree than its actual projective ratio field. -/
theorem homogeneous_output_trdeg_eq_projective_add_one
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (a : Fin 4) (ha : H a ≠ 0) :
    Algebra.trdeg K (polynomialOutputField H) =
      Algebra.trdeg K (projectiveRatioField (K := K)
        (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)) a) + 1 := by
  have hYa : algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H a) ≠ 0 := by
    intro hz
    apply ha
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
    simpa only [map_zero] using hz
  exact fullOutputField_trdeg_eq_projectiveRatioField_add_one _ a hYa
    (homogeneous_output_transcendental_over_projective_ratios H hd hH a ha)

/-- Every nonzero chart of the actual projective image of a rank-three
homogeneous map has transcendence degree exactly two over the original field. -/
theorem projective_image_ratio_field_trdeg_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (a : Fin 4) (ha : H a ≠ 0) :
    Algebra.trdeg K (projectiveRatioField (K := K)
      (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)) a) = 2 := by
  let R := projectiveRatioField (K := K)
    (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)) a
  have he := homogeneous_output_trdeg_eq_projective_add_one H hd hH a ha
  rw [(polynomialOutputField_trdeg_eq_rank H).trans (congrArg (fun n : ℕ => (n : Cardinal)) hrank)] at he
  change 3 = Algebra.trdeg K R + 1 at he
  have hle : Algebra.trdeg K R ≤ 3 := (self_le_add_right _ 1).trans_eq he.symm
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (hle.trans_lt (by simp))
  rw [hn] at he
  have hn' : 3 = n + 1 := by exact_mod_cast he
  have hn2 : n = 2 := by omega
  change Algebra.trdeg K R = 2
  rw [hn, hn2]
  rfl

/-- The actual projective chart's prime coordinate quotient has
function-field dimension two, with its exact original image relations. -/
theorem projective_image_chart_coordinate_function_field_trdeg_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (a : Fin 4) (ha : H a ≠ 0) :
    fiberCoordinateFunctionFieldTrdeg (L := K)
      (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i) /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H a)) = 2 := by
  exact (projectiveRatioCoordinateFunctionFieldEquiv (K := K)
    (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i)) a).trdeg_eq.trans
      (projective_image_ratio_field_trdeg_two H hd hH hrank a ha)

/-- Rank three constructs a genuine nonzero projective image chart
with the checked actual coordinate function-field dimension two. -/
theorem exists_projective_image_chart_dimension_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) :
    ∃ a : Fin 4, H a ≠ 0 ∧ fiberCoordinateFunctionFieldTrdeg (L := K)
      (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i) /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H a)) = 2 := by
  obtain ⟨a, ha⟩ : ∃ a, H a ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using rank_three_polynomial_map_ne_zero H hrank
  exact ⟨a, ha, projective_image_chart_coordinate_function_field_trdeg_two H hd hH hrank a ha⟩

end DimensionFourDependence
