import DimensionFourDependence.IntegralSchemeNormalization

/-! # Scheme isomorphisms retain the actual function-field point morphism -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Changing a stalk point along equality retains its actual
canonical morphism from the spectrum of that stalk. -/
theorem scheme_fromSpecStalk_congr
    {X : Scheme.{u}} {x y : X} (h : x = y) :
    Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq h)).inv ≫ X.fromSpecStalk y = X.fromSpecStalk x := by
  subst y
  simp [TopCat.Presheaf.stalkCongr]

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y)

/-- An actual scheme isomorphism induces its contravariant
isomorphism of the actual function-field stalks. -/
noncomputable def integralSchemeFunctionFieldIso : Y.functionField ≅ X.functionField :=
  (Y.presheaf.stalkCongr (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion e.hom))).symm ≪≫
    asIso (e.hom.stalkMap (genericPoint X))

/-- The induced field-spectrum isomorphism has the original direction
of the actual scheme isomorphism. -/
noncomputable def integralSchemeFunctionFieldSpectrumIso : Spec X.functionField ≅ Spec Y.functionField :=
  Scheme.Spec.mapIso (integralSchemeFunctionFieldIso e).op

/-- The actual function-field spectrum isomorphism commutes with
both actual generic-point morphisms, not merely their topological images. -/
theorem integralSchemeGenericPointMorphism_iso_naturality :
    (integralSchemeFunctionFieldSpectrumIso e).hom ≫ integralSchemeGenericPointMorphism Y =
      integralSchemeGenericPointMorphism X ≫ e.hom := by
  change Spec.map ((Y.presheaf.stalkCongr (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion e.hom))).inv ≫
      e.hom.stalkMap (genericPoint X)) ≫ Y.fromSpecStalk (genericPoint Y) =
    X.fromSpecStalk (genericPoint X) ≫ e.hom
  rw [Spec.map_comp, Category.assoc,
    scheme_fromSpecStalk_congr (genericPoint_eq_of_isOpenImmersion e.hom)]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk e.hom

end DimensionFourDependence
