import DimensionFourDependence.ProjectiveChartFunctionField
import DimensionFourDependence.HomogeneousEvaluationScaling
import DimensionFourDependence.ClosedGaussHomogeneousParameter

/-! # The closed Gauss parameter field in the projective source function field

Equal-degree homogeneous quotients are functions of projective coordinate
ratios. The constructed rational parameter therefore puts the entire
actual closed Gauss field inside every original-coefficient projective
source chart field. The parameter field remains relatively closed there.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Every quotient of equal-degree homogeneous forms is a function of
the projective coordinate ratios on a nonzero source chart. -/
theorem homogeneous_quotient_mem_projective_chart_field
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0)
    (p q : MvPolynomial (Fin 4) K) {d : ℕ}
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d) :
    aeval x p / aeval x q ∈ projectiveCoordinateChartField (C := K) x a := by
  let L := projectiveCoordinateChartField (C := K) x a
  let y : Fin 4 → L := fun i => ⟨x i / x a, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hy (r : MvPolynomial (Fin 4) K) :
      ((aeval y r : L) : F) = aeval (fun i => x i / x a) r :=
    MvPolynomial.comp_aeval_apply y L.val r
  have he (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous d) :
      aeval (fun i => x i / x a) r = (x a)⁻¹ ^ d * aeval x r := by
    simpa only [div_eq_mul_inv, mul_comm] using homogeneous_aeval_scale r hr x (x a)⁻¹
  have hmem := L.div_mem (aeval y p).property (aeval y q).property
  rw [hy p, hy q, he p hp, he q hq] at hmem
  simpa only [mul_div_mul_left _ _ (pow_ne_zero d (inv_ne_zero ha))] using hmem

/-- Evaluation at the original rational source coordinates is the
canonical polynomial-to-source-function-field map. -/
theorem rationalCoordinate_aeval {n : ℕ} (p : MvPolynomial (Fin n) K) :
    aeval (rationalCoordinate (K := K) (n := n)) p =
      algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) p := by
  have h : aeval (rationalCoordinate (K := K) (n := n)) =
      Algebra.algHom K (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [aeval_X]
    rfl
  exact AlgHom.congr_fun h p

variable [CharZero K]

/-- The actual relatively closed Gauss parameter field is already inside
the projective source field over the original coefficients. -/
theorem actual_closed_gauss_parameter_field_le_projective_source_chart
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (a : Fin 4) :
    closedGaussParameterField H I ≤ projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) a := by
  obtain ⟨p, q, D, hD, hp0, hq0, hp, hq, hrel, hrep⟩ :=
    actual_closed_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  rw [← closedGaussParameterSourceHom_X_adjoin H I e]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨rfl⟩
  rw [hrep]
  have ha : rationalCoordinate (K := K) a ≠ 0 := by
    simpa only [rationalCoordinate, map_zero] using
      (IsFractionRing.injective (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))).ne
        (X_ne_zero a)
  change algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
    algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q ∈
      projectiveCoordinateChartField (C := K) (rationalCoordinate (K := K) (n := 4)) a
  simpa only [rationalCoordinate_aeval] using
    homogeneous_quotient_mem_projective_chart_field (rationalCoordinate (K := K) (n := 4)) a ha p q hp hq

/-- The actual parameter inclusion supplies the coefficient action on
the original projective source function field. -/
@[instance_reducible]
noncomputable def closedGaussProjectiveSourceAlgebra
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (a : Fin 4) :
    Algebra (closedGaussParameterField H I) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) a) :=
  (IntermediateField.inclusion (actual_closed_gauss_parameter_field_le_projective_source_chart H hH I e a)).toRingHom.toAlgebra

/-- The projective source coefficient action and the actual inclusion in
the original source function field form the same scalar tower. -/
theorem closedGaussProjectiveSource_scalarTower
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (a : Fin 4) :
    letI : Algebra (closedGaussParameterField H I) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) a) := closedGaussProjectiveSourceAlgebra H hH I e a
    IsScalarTower (closedGaussParameterField H I) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) a) (FractionRing (MvPolynomial (Fin 4) K)) := by
  let : Algebra (closedGaussParameterField H I) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) a) := closedGaussProjectiveSourceAlgebra H hH I e a
  exact IsScalarTower.of_algebraMap_eq (by intro c; rfl)

/-- Adjoining the projective ratios over the closed Gauss field gives
exactly the original-coefficient projective source function field. -/
theorem actual_closed_gauss_projective_chart_field_eq_original
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (a : Fin 4) :
    (projectiveCoordinateChartField (C := closedGaussParameterField H I)
      (rationalCoordinate (K := K) (n := 4)) a).restrictScalars K =
      projectiveCoordinateChartField (C := K) (rationalCoordinate (K := K) (n := 4)) a := by
  let L := projectiveCoordinateChartField (C := K) (rationalCoordinate (K := K) (n := 4)) a
  have hC := actual_closed_gauss_parameter_field_le_projective_source_chart H hH I e a
  apply le_antisymm
  · have hle : projectiveCoordinateChartField (C := closedGaussParameterField H I)
        (rationalCoordinate (K := K) (n := 4)) a ≤ IntermediateField.extendScalars hC := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
    exact hle
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin (closedGaussParameterField H I) _ ⟨i, rfl⟩

/-- The actual Gauss parameter field remains relatively closed in the
projective source field; the extra radial source coordinate is unnecessary. -/
theorem actual_closed_gauss_parameter_relatively_closed_in_projective_source
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (a : Fin 4) :
    letI : Algebra (closedGaussParameterField H I) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) a) := closedGaussProjectiveSourceAlgebra H hH I e a
    algebraicClosure (closedGaussParameterField H I) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) a) = ⊥ := by
  let L := projectiveCoordinateChartField (C := K) (rationalCoordinate (K := K) (n := 4)) a
  let : Algebra (closedGaussParameterField H I) L := closedGaussProjectiveSourceAlgebra H hH I e a
  let : IsScalarTower (closedGaussParameterField H I) L (FractionRing (MvPolynomial (Fin 4) K)) :=
    closedGaussProjectiveSource_scalarTower H hH I e a
  apply le_antisymm ?_ bot_le
  intro z hz
  have hm : (z : FractionRing (MvPolynomial (Fin 4) K)) ∈
      algebraicClosure (closedGaussParameterField H I) (FractionRing (MvPolynomial (Fin 4) K)) :=
    mem_algebraicClosure_iff.mpr ((mem_algebraicClosure_iff.mp hz).algHom
      (IsScalarTower.toAlgHom (closedGaussParameterField H I) L (FractionRing (MvPolynomial (Fin 4) K))))
  rw [closedGaussParameterField_relatively_closed, IntermediateField.mem_bot] at hm
  obtain ⟨c, hc⟩ := hm
  apply IntermediateField.mem_bot.mpr
  refine ⟨c, ?_⟩
  apply Subtype.val_injective
  exact hc

end DimensionFourDependence
