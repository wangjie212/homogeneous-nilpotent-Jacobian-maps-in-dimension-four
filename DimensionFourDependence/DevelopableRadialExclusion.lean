import DimensionFourDependence.GaussCurvePrimitiveParameter
import DimensionFourDependence.ParametrizedNormalRadialExclusion
import DimensionFourDependence.ZeroDimensionalGaussImage

/-! # Section 4.1: the actual developable image has nonzero radial pairing

The actual dimension-one Gauss field supplies its rational parameter
and primitive polynomial covector. The rational-section obstruction
then makes zero radial pairing force constant component dependence.
The zero-dimensional case is already checked. Thus a nonplanar original
homogeneous image with Gauss dimension at most one has nonzero pairing.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Zero radial pairing for an actual one-dimensional Gauss image
forces an original-field component relation. The actual primitive
rational parameter presentation is constructed, rather than assumed. -/
theorem dependence_of_gauss_dimension_one_zero_radial_pairing
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1)
    (hradial : ∑ i, rationalImageNormal H I.equation i * rationalCoordinate (K := K) i = 0) :
    ComponentsDependent H := by
  obtain ⟨v, hv, hprimitive, t, c, _, hrep⟩ := actual_gauss_curve_primitive_polynomial_parameter H I hGauss
  exact dependence_of_parametrized_zero_radial_image_normal H hd hH I v hv hprimitive t c hrep hradial

/-- The full zero-radial-pairing obstruction in Section 4.1, including
both point and curve Gauss images, over the original characteristic-zero field. -/
theorem dependence_of_gauss_dimension_le_one_zero_radial_pairing
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I ≤ 1)
    (hradial : ∑ i, rationalImageNormal H I.equation i * rationalCoordinate (K := K) i = 0) :
    ComponentsDependent H := by
  rcases Cardinal.le_one_iff.mp hGauss with hzero | hone
  · exact componentsDependent_of_gauss_image_dimension_zero H hd hH I hzero
  · exact dependence_of_gauss_dimension_one_zero_radial_pairing H hd hH I hone hradial

/-- For an actual nonplanar original homogeneous image with Gauss
dimension at most one, the actual normal/source radial pairing is nonzero. -/
theorem independent_developable_image_radial_pairing_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I ≤ 1) :
    (∑ i, rationalImageNormal H I.equation i * rationalCoordinate (K := K) i) ≠ 0 :=
  fun h => hind (dependence_of_gauss_dimension_le_one_zero_radial_pairing H hd hH I hGauss h)

end DimensionFourDependence
