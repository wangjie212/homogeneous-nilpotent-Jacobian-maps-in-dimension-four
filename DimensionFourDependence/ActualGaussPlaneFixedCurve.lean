import DimensionFourDependence.NormalPlaneConstantIntersection
import DimensionFourDependence.PolynomialPlaneParameterRigidity
import DimensionFourDependence.ExtendedChosenGaussRuling
import DimensionFourDependence.MovingPlanePointFieldDimension

/-! # The actual Gauss tangent-plane family has no fixed curve at an independent parameter -/

namespace DimensionFourDependence

open Matrix Module

universe u

set_option maxHeartbeats 2000000

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
  (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "ν₀" => gaussParameterNormal H I (actualGaussRulingParameterChoice H I hH hd hind hGauss)

/-- The original nonplanar map constructs an actual primitive
polynomial representative of its Gauss planes whose entire constant
coefficient kernel has dimension at most one. -/
theorem exists_actual_gauss_plane_polynomial_constant_kernel
    : ∃ v : Fin 4 → Polynomial K, v ≠ 0 ∧
      (∀ p : Polynomial K, (∀ i, p ∣ v i) → IsUnit p) ∧
      ∃ r : RatFunc K, r ≠ 0 ∧ (∀ i, ν₀ i = r * algebraMap (Polynomial K) (RatFunc K) (v i)) ∧
        finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1 := by
  have hLI := actualGaussRulingParameterChoice_jet_independent H I hH hd hind hGauss
  have hw : ν₀ ≠ 0 := hLI.ne_zero (0 : Fin 3)
  obtain ⟨v, hv, hprimitive, r, hr, hrep⟩ := rational_vector_primitive_polynomial_presentation ν₀ hw
  exact ⟨v, hv, hprimitive, r, hr, hrep,
    polynomial_normal_coefficient_kernel_finrank_le_one ν₀ v r hLI hrep⟩

variable {E L : Type u} [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]

/-- The actual Gauss plane family has one original constant vector
containing every incident point at every parameter independent of that
point's field. Thus its fixed projective part is at most one point. -/
theorem exists_actual_gauss_plane_polynomial_constant_point_line
    : ∃ v : Fin 4 → Polynomial K, v ≠ 0 ∧
      (∀ p : Polynomial K, (∀ i, p ∣ v i) → IsUnit p) ∧
      ∃ r : RatFunc K, r ≠ 0 ∧ (∀ i, ν₀ i = r * algebraMap (Polynomial K) (RatFunc K) (v i)) ∧
        ∃ c : Fin 4 → K, ∀ (x : Fin 4 → E) (t : L), Transcendental E t →
          (∑ i, algebraMap E L (x i) * Polynomial.aeval t (v i) = 0) →
            ∃ a : E, x = a • (fun i => algebraMap K E (c i)) := by
  obtain ⟨v, hv, hprimitive, r, hr, hrep, hdim⟩ :=
    exists_actual_gauss_plane_polynomial_constant_kernel H I hH hd hind hGauss
  obtain ⟨c, _hc, hgen⟩ := matrix_kernel_finrank_le_one_constant_generator (E := E)
    (polynomialCovectorCoefficientMatrix v) hdim
  exact ⟨v, hv, hprimitive, r, hr, hrep, c, fun x t ht hp => hgen x
    (transcendental_parameter_plane_incidence_mem_coefficient_kernel v x t ht hp)⟩

/-- If an original projective point varies in a curve and lies in
the actual Gauss plane family, its Gauss parameter is algebraic over the
point field. The primitive plane family and constant-intersection bound
are constructed from the original map, not supplied. -/
theorem exists_actual_gauss_plane_polynomial_no_independent_fixed_curve
    : ∃ v : Fin 4 → Polynomial K, v ≠ 0 ∧
      (∀ p : Polynomial K, (∀ i, p ∣ v i) → IsUnit p) ∧
      ∃ r : RatFunc K, r ≠ 0 ∧ (∀ i, ν₀ i = r * algebraMap (Polynomial K) (RatFunc K) (v i)) ∧
        ∀ (x : Fin 4 → E) (t : L),
          (∑ i, algebraMap E L (x i) * Polynomial.aeval t (v i) = 0) →
          ∀ a : Fin 4, x a ≠ 0 →
            Algebra.trdeg K (projectiveCoordinateChartField (C := K) x a) ≠ 0 → IsAlgebraic E t := by
  obtain ⟨v, hv, hprimitive, r, hr, hrep, hdim⟩ :=
    exists_actual_gauss_plane_polynomial_constant_kernel H I hH hd hind hGauss
  exact ⟨v, hv, hprimitive, r, hr, hrep, fun x t hp a ha hcurve =>
    polynomial_plane_parameter_isAlgebraic_over_nonconstant_point v hdim x t hp a ha hcurve⟩

/-- For the actual Gauss plane family, a two-dimensional family
field algebraic over the point coordinates and the Gauss parameter has
a two-dimensional source point field. The polynomial plane family is
constructed from the original map, without a normal-span hypothesis. -/
theorem exists_actual_gauss_plane_polynomial_source_point_dimension_two
    (t : L) [Algebra.IsAlgebraic (IntermediateField.adjoin E {t}) L]
    (hL : Algebra.trdeg K L = 2)
    : ∃ v : Fin 4 → Polynomial K, v ≠ 0 ∧
      (∀ p : Polynomial K, (∀ i, p ∣ v i) → IsUnit p) ∧
      ∃ r : RatFunc K, r ≠ 0 ∧ (∀ i, ν₀ i = r * algebraMap (Polynomial K) (RatFunc K) (v i)) ∧
        ∀ (x : Fin 4 → E) (a : Fin 4), x a ≠ 0 →
          projectiveCoordinateChartField (C := K) x a = ⊤ →
          (∑ i, algebraMap E L (x i) * Polynomial.aeval t (v i) = 0) → Algebra.trdeg K E = 2 := by
  obtain ⟨v, hv, hprimitive, r, hr, hrep, hdim⟩ :=
    exists_actual_gauss_plane_polynomial_constant_kernel H I hH hd hind hGauss
  exact ⟨v, hv, hprimitive, r, hr, hrep, fun x a ha hgen hp =>
    polynomial_moving_plane_incidence_source_point_trdeg_two v hdim t hL x a ha hgen hp⟩

end DimensionFourDependence
