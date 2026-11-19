import DimensionFourDependence.PolynomialCovectorCoefficientKernel
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Actual rational normal planes and their polynomial representatives agree -/

namespace DimensionFourDependence

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A rational-parameter embedding evaluates each original polynomial
at the actual image of the parameter. -/
theorem rational_parameter_hom_polynomial_value
    (φ : RatFunc K →ₐ[K] L) (p : Polynomial K) :
    φ (algebraMap (Polynomial K) (RatFunc K) p) = Polynomial.aeval (φ RatFunc.X) p :=
  (congrArg φ (RatFunc.aeval_X_left_eq_algebraMap p)).symm.trans
    (Polynomial.aeval_algHom_apply φ RatFunc.X p).symm

/-- Clearing the common rational factor from a normal vector
retains exactly the same plane equation, with its actual parameter value. -/
theorem rational_normal_plane_polynomial_value
    (φ : RatFunc K →ₐ[K] L) (ν : Fin 4 → RatFunc K)
    (v : Fin 4 → Polynomial K) (r : RatFunc K)
    (hrep : ∀ i, ν i = r * algebraMap (Polynomial K) (RatFunc K) (v i))
    (x : Fin 4 → L) :
    (∑ i, x i * φ (ν i)) =
      φ r * ∑ i, x i * Polynomial.aeval (φ RatFunc.X) (v i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hrep i, map_mul, rational_parameter_hom_polynomial_value]
  ring

/-- A nonzero common rational factor makes incidence in the actual
rational normal plane equivalent to incidence in its polynomial
representative. No nonzero-specialization hypothesis is needed. -/
theorem rational_normal_plane_incidence_iff_polynomial
    (φ : RatFunc K →ₐ[K] L) (ν : Fin 4 → RatFunc K)
    (v : Fin 4 → Polynomial K) (r : RatFunc K) (hr : r ≠ 0)
    (hrep : ∀ i, ν i = r * algebraMap (Polynomial K) (RatFunc K) (v i))
    (x : Fin 4 → L) :
    (∑ i, x i * φ (ν i)) = 0 ↔
      (∑ i, x i * Polynomial.aeval (φ RatFunc.X) (v i)) = 0 := by
  rw [rational_normal_plane_polynomial_value φ ν v r hrep x, mul_eq_zero]
  exact or_iff_right ((map_ne_zero φ).mpr hr)

end DimensionFourDependence
