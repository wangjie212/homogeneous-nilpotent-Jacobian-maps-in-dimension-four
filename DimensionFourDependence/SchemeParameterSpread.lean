import DimensionFourDependence.SchemeSpreadOutImage
import DimensionFourDependence.ReducedPointClosureScheme
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Actual integral spread-out schemes in a source-parameter product

A generic curve is sent to the product of its source and parameter
model. Its reduced point closure gives the actual integral family.
The closed source image agrees with that of the original generic curve.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {B X Y T C : Scheme.{u}}

/-- The actual product of the source and the parameter model over
their common base scheme. -/
noncomputable def parameterSpreadAmbient (x : X ⟶ B) (c : C ⟶ B) : Scheme.{u} :=
  pullback x c

/-- The generic source and parameter projections give an actual
morphism into the source-parameter product. -/
noncomputable def parameterSpreadMorphism
    (x : X ⟶ B) (c : C ⟶ B) (f : Y ⟶ X) (r : Y ⟶ T) (η : T ⟶ C)
    (h : f ≫ x = r ≫ η ≫ c) : Y ⟶ parameterSpreadAmbient x c :=
  pullback.lift f (r ≫ η) (by simpa only [Category.assoc] using h)

/-- The actual product morphism retains the entire source map. -/
theorem parameterSpreadMorphism_fst
    (x : X ⟶ B) (c : C ⟶ B) (f : Y ⟶ X) (r : Y ⟶ T) (η : T ⟶ C)
    (h : f ≫ x = r ≫ η ≫ c) :
    parameterSpreadMorphism x c f r η h ≫ pullback.fst x c = f :=
  pullback.lift_fst _ _ _

/-- The actual product morphism retains the entire parameter map. -/
theorem parameterSpreadMorphism_snd
    (x : X ⟶ B) (c : C ⟶ B) (f : Y ⟶ X) (r : Y ⟶ T) (η : T ⟶ C)
    (h : f ≫ x = r ≫ η ≫ c) :
    parameterSpreadMorphism x c f r η h ≫ pullback.snd x c = r ≫ η :=
  pullback.lift_snd _ _ _

/-- The actual reduced integral family obtained by closing the generic
point of the given prime subvariety in the source-parameter product. -/
noncomputable def parameterSpreadCurveFamilyScheme
    (x : X ⟶ B) (c : C ⟶ B) (f : Y ⟶ X) (r : Y ⟶ T) (η : T ⟶ C)
    (h : f ≫ x = r ≫ η ≫ c) (Z : Set Y) (hZ : IsIrreducible Z) : Scheme.{u} :=
  reducedPointClosureScheme (parameterSpreadAmbient x c)
    (parameterSpreadMorphism x c f r η h hZ.genericPoint)

/-- Its actual closed inclusion into the source-parameter product. -/
noncomputable def parameterSpreadCurveFamilyInclusion
    (x : X ⟶ B) (c : C ⟶ B) (f : Y ⟶ X) (r : Y ⟶ T) (η : T ⟶ C)
    (h : f ≫ x = r ≫ η ≫ c) (Z : Set Y) (hZ : IsIrreducible Z) :
    parameterSpreadCurveFamilyScheme x c f r η h Z hZ ⟶ parameterSpreadAmbient x c :=
  reducedPointClosureInclusion _ _

/-- The spread-out family's actual morphism to the original source. -/
noncomputable def parameterSpreadCurveFamilySourceMorphism
    (x : X ⟶ B) (c : C ⟶ B) (f : Y ⟶ X) (r : Y ⟶ T) (η : T ⟶ C)
    (h : f ≫ x = r ≫ η ≫ c) (Z : Set Y) (hZ : IsIrreducible Z) :
    parameterSpreadCurveFamilyScheme x c f r η h Z hZ ⟶ X :=
  parameterSpreadCurveFamilyInclusion x c f r η h Z hZ ≫ pullback.fst x c

/-- The constructed family is integral without assuming a surface
or a chosen affine normalization model. -/
theorem parameterSpreadCurveFamilyScheme_isIntegral
    (x : X ⟶ B) (c : C ⟶ B) (f : Y ⟶ X) (r : Y ⟶ T) (η : T ⟶ C)
    (h : f ≫ x = r ≫ η ≫ c) (Z : Set Y) (hZ : IsIrreducible Z) :
    IsIntegral (parameterSpreadCurveFamilyScheme x c f r η h Z hZ) :=
  reducedPointClosureScheme_isIntegral _ _

/-- Its actual underlying closed set is precisely the closure of the
original prime subvariety under the specified generic product map. -/
theorem parameterSpreadCurveFamilyInclusion_range
    (x : X ⟶ B) (c : C ⟶ B) (f : Y ⟶ X) (r : Y ⟶ T) (η : T ⟶ C)
    (h : f ≫ x = r ≫ η ≫ c) (Z : Set Y) (hZ : IsIrreducible Z)
    (hZclosed : IsClosed Z) :
    Set.range (parameterSpreadCurveFamilyInclusion x c f r η h Z hZ) =
      closure (parameterSpreadMorphism x c f r η h '' Z) := by
  exact (reducedPointClosureInclusion_range _ _).trans
    (scheme_spread_out_generic_point (parameterSpreadMorphism x c f r η h) Z hZ hZclosed).def

/-- Density of the actual spread-out family's source image is exactly
density of the original generic curve's source image. -/
theorem parameterSpreadCurveFamilySourceMorphism_image_closure
    (x : X ⟶ B) (c : C ⟶ B) (f : Y ⟶ X) (r : Y ⟶ T) (η : T ⟶ C)
    (h : f ≫ x = r ≫ η ≫ c) (Z : Set Y) (hZ : IsIrreducible Z)
    (hZclosed : IsClosed Z) :
    closure (Set.range (parameterSpreadCurveFamilySourceMorphism x c f r η h Z hZ)) =
      closure (f '' Z) := by
  change closure (Set.range (pullback.fst x c ∘
    parameterSpreadCurveFamilyInclusion x c f r η h Z hZ)) = _
  rw [Set.range_comp, parameterSpreadCurveFamilyInclusion_range _ _ _ _ _ _ _ _ hZclosed]
  exact scheme_spread_out_source_image_closure (parameterSpreadMorphism x c f r η h)
    (pullback.fst x c) f (parameterSpreadMorphism_fst x c f r η h) Z

end DimensionFourDependence
