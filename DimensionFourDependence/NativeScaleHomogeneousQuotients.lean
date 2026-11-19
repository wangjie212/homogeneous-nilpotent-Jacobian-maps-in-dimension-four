import DimensionFourDependence.NativeIndependentScaleSource
import DimensionFourDependence.IndependentScaleHomogeneousValues

/-! # Original equal-degree fractions retain their native degree-zero values -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

local instance nativeScaleHomogeneousQuotientsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeScaleHomogeneousQuotientsExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
noncomputable local instance nativeScaleHomogeneousQuotientsOriginalAlgebra : Algebra K (N).functionField :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

/-- An original homogeneous polynomial retains its native value,
its exact frame denominator, and its independent radial degree. -/
theorem nativeIndependentScaleSourceFieldHom_homogeneous_polynomial
    (L : MvPolynomial (Fin 4) E) (hL : aeval (R := E) (w) L ≠ 0)
    (P : MvPolynomial (Fin 4) K) {D : ℕ} (hP : P.IsHomogeneous D) :
    nativeIndependentScaleSourceFieldHom H I E hH e L hL (algebraMap _ S₀ P) =
      RatFunc.X ^ D * RatFunc.C
        (aeval (R := E) (w) (MvPolynomial.map (ι) P) / (aeval (R := E) (w) L) ^ D) := by
  rw [nativeIndependentScaleSourceFieldHom_extended_polynomial,
    independent_scale_homogeneous_polynomial_value _ (hP.map (ι))]
  congr 1
  congr 1
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
    homogeneous_aeval_scale_indexed (MvPolynomial.map (ι) P) (hP.map (ι))
      (w) (aeval (R := E) (w) L)⁻¹

/-- The independent scale and normalization frame cancel from every
equal-degree original homogeneous quotient. Its image is the constant
rational function of the exact native quotient. -/
theorem nativeIndependentScaleSourceFieldHom_homogeneous_quotient
    (L : MvPolynomial (Fin 4) E) (hL : aeval (R := E) (w) L ≠ 0)
    (P Q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hP : P.IsHomogeneous D) (hQ : Q.IsHomogeneous D) :
    nativeIndependentScaleSourceFieldHom H I E hH e L hL
      (algebraMap _ S₀ P / algebraMap _ S₀ Q) =
      RatFunc.C (aeval (R := E) (w) (MvPolynomial.map (ι) P) /
        aeval (R := E) (w) (MvPolynomial.map (ι) Q)) := by
  rw [map_div₀, nativeIndependentScaleSourceFieldHom_homogeneous_polynomial H I E hH e L hL P hP,
    nativeIndependentScaleSourceFieldHom_homogeneous_polynomial H I E hH e L hL Q hQ,
    mul_div_mul_left _ _ (pow_ne_zero D RatFunc.X_ne_zero), ← map_div₀,
    div_div_div_cancel_right₀ (pow_ne_zero D hL)]

end DimensionFourDependence
