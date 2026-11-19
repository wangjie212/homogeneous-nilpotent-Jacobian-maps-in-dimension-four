import DimensionFourDependence.SchemeRationalSectionFunctions

/-! # Affine coordinate fields retain the actual scheme rational values -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u v w

variable (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
  (hU : IsAffineOpen U) (R : Type v) [CommRing R]
  (F : Type w) [CommRing F] [Algebra R F] [IsFractionRing R F]
  (e : Γ(X, U) ≃+* R)

/-- An actual affine section identification induces the coordinate
fraction field's identification with the scheme's own function field. -/
noncomputable def affineChartFunctionFieldEquiv : F ≃+* X.functionField := by
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsFractionRing.ringEquivOfRingEquiv e.symm

/-- The field identification agrees with the actual generic germ of
every regular affine-chart function. -/
theorem affineChartFunctionFieldEquiv_section (r : Γ(X, U)) :
    affineChartFunctionFieldEquiv X U hU R F e (algebraMap R F (e r)) =
      X.germToFunctionField U r := by
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  simpa only [affineChartFunctionFieldEquiv, RingEquiv.symm_apply_apply,
    RingHom.algebraMap_toAlgebra] using
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (K := F) (L := X.functionField) e.symm (e r))

/-- At every point of the chart, the identified rational value is the
image of the function's actual local-ring germ. -/
theorem affineChartFunctionFieldEquiv_section_at_point (r : Γ(X, U)) (p : U) :
    affineChartFunctionFieldEquiv X U hU R F e (algebraMap R F (e r)) =
      schemeRationalSectionFunction X U r p := by
  rw [affineChartFunctionFieldEquiv_section,
    schemeRationalSectionFunction_eq_generic]

/-- The inverse identification retains the entire original affine
coordinate value of every actual generic germ. -/
theorem affineChartFunctionFieldEquiv_symm_section (r : Γ(X, U)) :
    (affineChartFunctionFieldEquiv X U hU R F e).symm
      (X.germToFunctionField U r) = algebraMap R F (e r) := by
  apply (affineChartFunctionFieldEquiv X U hU R F e).injective
  rw [RingEquiv.apply_symm_apply, affineChartFunctionFieldEquiv_section]

end DimensionFourDependence
