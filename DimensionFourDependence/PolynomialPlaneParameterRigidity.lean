import DimensionFourDependence.PolynomialCovectorCoefficientKernel
import DimensionFourDependence.SmallKernelScalarExtension
import DimensionFourDependence.ProjectiveChartFunctionField

/-! # A nonconstant projective point forces algebraic dependence of a moving-plane parameter -/

namespace DimensionFourDependence

open Matrix Module

variable {K E L : Type*} [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]

/-- With constant plane intersection of dimension at most one,
incidence at a parameter independent of the point field makes the entire
original projective coordinate field constant. -/
theorem polynomial_plane_transcendental_parameter_coordinate_field_eq_bot
    (v : Fin 4 → Polynomial K)
    (hdim : finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (x : Fin 4 → E) (t : L) (ht : Transcendental E t)
    (hplane : ∑ i, algebraMap E L (x i) * Polynomial.aeval t (v i) = 0)
    (a : Fin 4) (ha : x a ≠ 0) : projectiveCoordinateChartField (C := K) x a = ⊥ := by
  obtain ⟨b, _hba, hb⟩ := small_matrix_kernel_projective_ratios_descend
    (polynomialCovectorCoefficientMatrix v) hdim x
    (transcendental_parameter_plane_incidence_mem_coefficient_kernel v x t ht hplane) a ha
  apply bot_unique
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  change x i / x a ∈ (⊥ : IntermediateField K E)
  rw [hb i]
  exact (⊥ : IntermediateField K E).algebraMap_mem (b i)

/-- The independent-parameter incidence point has zero-dimensional
actual projective coordinate field over the original constants. -/
theorem polynomial_plane_transcendental_parameter_coordinate_field_trdeg_zero
    (v : Fin 4 → Polynomial K)
    (hdim : finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (x : Fin 4 → E) (t : L) (ht : Transcendental E t)
    (hplane : ∑ i, algebraMap E L (x i) * Polynomial.aeval t (v i) = 0)
    (a : Fin 4) (ha : x a ≠ 0) :
    Algebra.trdeg K (projectiveCoordinateChartField (C := K) x a) = 0 := by
  rw [polynomial_plane_transcendental_parameter_coordinate_field_eq_bot v hdim x t ht hplane a ha]
  exact trdeg_eq_zero

/-- A point with nonconstant original projective coordinate field
lying in this family forces the plane parameter algebraic over its point
field. Thus a fixed curve cannot coexist with an independent parameter. -/
theorem polynomial_plane_parameter_isAlgebraic_over_nonconstant_point
    (v : Fin 4 → Polynomial K)
    (hdim : finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (x : Fin 4 → E) (t : L)
    (hplane : ∑ i, algebraMap E L (x i) * Polynomial.aeval t (v i) = 0)
    (a : Fin 4) (ha : x a ≠ 0)
    (hcurve : Algebra.trdeg K (projectiveCoordinateChartField (C := K) x a) ≠ 0) :
    IsAlgebraic E t := by
  by_contra ht
  exact hcurve (polynomial_plane_transcendental_parameter_coordinate_field_trdeg_zero
    v hdim x t ht hplane a ha)

end DimensionFourDependence
