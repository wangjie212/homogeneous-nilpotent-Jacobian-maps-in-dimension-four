import DimensionFourDependence.ActualGaussPlaneFixedCurve
import DimensionFourDependence.RationalPlanePolynomialSpecialization

/-! # Polynomial incidence for an embedded actual Gauss tangent plane -/

namespace DimensionFourDependence

variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
  (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

/-- Incidence in the actual chosen Gauss plane supplies both a
polynomial equation at the same parameter and its small constant kernel. -/
theorem actual_gauss_plane_polynomial_incidence_of_parameter_embedding
    (φ : RatFunc K →ₐ[K] L) (x : Fin 4 → L)
    (hplane : ∑ i, x i * φ (gaussParameterNormal H I
      (actualGaussRulingParameterChoice H I hH hd hind hGauss) i) = 0) :
    ∃ v : Fin 4 → Polynomial K,
      Module.finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1 ∧
      ∑ i, x i * Polynomial.aeval (φ RatFunc.X) (v i) = 0 := by
  obtain ⟨v, _hv, _hprimitive, r, hr, hrep, hdim⟩ :=
    exists_actual_gauss_plane_polynomial_constant_kernel H I hH hd hind hGauss
  exact ⟨v, hdim, (rational_normal_plane_incidence_iff_polynomial φ _ v r hr hrep x).mp hplane⟩

end DimensionFourDependence
