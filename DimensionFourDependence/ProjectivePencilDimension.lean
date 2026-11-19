import DimensionFourDependence.ProjectiveSourceCoordinates
import DimensionFourDependence.ProjectivePencilFunctionField

/-! # The actual original projective pencil charts have dimension two

The original source chart is a polynomial algebra in its three genuine
coordinate ratios. Its fraction field therefore has transcendence degree
three. The actual closed Gauss parameter has transcendence degree one,
so the actual pencil coordinate algebra has relative degree two.
-/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type u} [Field K]

/-- The original projective source field has its expected three
independent parameters, through the actual original coordinate chart. -/
theorem original_projective_chart_field_trdeg_three
    (s : Fin 4 ≃ Option (Fin 3)) :
    Algebra.trdeg K (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) = 3 := by
  let A := projectiveCoordinateChartAlgebra (C := K)
    (rationalCoordinate (K := K) (n := 4)) (s.symm none)
  let L := projectiveCoordinateChartField (C := K)
    (rationalCoordinate (K := K) (n := 4)) (s.symm none)
  have hA : Algebra.trdeg K A = 3 := by
    rw [← (projectiveSourceFullChartCoordinateEquiv (K := K) s).trdeg_eq]
    simp [MvPolynomial.trdeg_of_isDomain]
  letI : IsScalarTower K A L := IsScalarTower.of_algebraMap_eq (by
    intro c
    apply Subtype.val_injective
    rfl)
  letI : Algebra.IsAlgebraic A L := IsLocalization.isAlgebraic L (nonZeroDivisors A)
  have h := trdeg_add_eq (A := L) K A
  simpa only [hA, trdeg_eq_zero, add_zero] using h.symm

variable [CharZero K]

/-- The original source field is a function field of two variables over
the actual closed Gauss parameter, with its actual inclusion action. -/
theorem closed_gauss_projective_source_trdeg_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hGauss : gaussImageDimension H I = 1) (s : Fin 4 ≃ Option (Fin 3)) :
    letI : Algebra (closedGaussParameterField H I) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) :=
        closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
    Algebra.trdeg (closedGaussParameterField H I) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) = 2 := by
  let C := closedGaussParameterField H I
  let L := projectiveCoordinateChartField (C := K)
    (rationalCoordinate (K := K) (n := 4)) (s.symm none)
  letI : Algebra C L := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  letI : IsScalarTower K C L := IsScalarTower.of_algebraMap_eq (by intro c; rfl)
  have h := trdeg_add_eq (A := L) K C
  rw [closedGaussParameterField_trdeg_one H I hGauss,
    original_projective_chart_field_trdeg_three s] at h
  have hle : Algebra.trdeg C L ≤ 3 := le_add_self.trans_eq h
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (hle.trans_lt (by simp))
  rw [hn] at h
  have hn' : 1 + n = 3 := by exact_mod_cast h
  have hn2 : n = 2 := by omega
  rw [hn, hn2]
  rfl

/-- Every actual affine projective-pencil chart is a surface over its
actual closed parameter field, before any chosen normalization divisor. -/
theorem actual_closed_gauss_pencil_chart_trdeg_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hGauss : gaussImageDimension H I = 1) (s : Fin 4 ≃ Option (Fin 3)) :
    Algebra.trdeg (closedGaussParameterField H I) (closedGaussPencilChartAlgebra H I s) = 2 := by
  let C := closedGaussParameterField H I
  let R₀ := projectiveCoordinateChartAlgebra (C := K)
    (rationalCoordinate (K := K) (n := 4)) (s.symm none)
  let A := projectiveCoordinateChartAlgebra (C := C)
    (rationalCoordinate (K := K) (n := 4)) (s.symm none)
  let L := projectiveCoordinateChartField (C := K)
    (rationalCoordinate (K := K) (n := 4)) (s.symm none)
  letI : Algebra C L := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  letI : Algebra R₀ A := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  letI : Algebra A L := projectivePencilSourceFieldAlgebra H I s hH e
  letI : IsScalarTower C A L := IsScalarTower.of_algebraMap_eq
    (fun c => (projectivePencilSourceFieldHom H I s hH e).commutes c |>.symm)
  letI : IsFractionRing A L := actual_projective_pencil_source_isFractionRing H I s hH e
  letI : Algebra.IsAlgebraic A L := IsLocalization.isAlgebraic L (nonZeroDivisors A)
  have h := trdeg_add_eq (A := L) C A
  have hzero : Algebra.trdeg A L = 0 := trdeg_eq_zero
  rw [hzero, add_zero, closed_gauss_projective_source_trdeg_two H hH I e hGauss s] at h
  rw [closedGaussPencilChartAlgebra_eq_projectiveCoordinateChart]
  exact h

end DimensionFourDependence
