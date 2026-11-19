import DimensionFourDependence.ProjectiveCoefficientChartMaps

/-! # Projective coefficient extension commutes with the actual base morphisms -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry HomogeneousLocalization CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C E : Type u} [CommRing C] [CommRing E] (f : C →+* E)

/-- The actual graded localization map sends original field-base
constants to the same constants over the extended coefficient ring. -/
theorem polynomialCoefficientAwayMap_base_constant
    (v : MvPolynomial (Fin 4) C) (c : C) :
    HomogeneousLocalization.Away.map (polynomialCoefficientGradedHom f) v
        (fromZeroRingHom (homogeneousSubmodule (Fin 4) C) (.powers v)
          ((polynomialProjectiveDegreeZeroEquiv C).symm c)) =
      fromZeroRingHom (homogeneousSubmodule (Fin 4) E)
        (.powers (MvPolynomial.map f v)) ((polynomialProjectiveDegreeZeroEquiv E).symm (f c)) := by
  apply HomogeneousLocalization.val_injective
  simp [fromZeroRingHom, HomogeneousLocalization.Away.map,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    polynomialCoefficientGradedHom, polynomialProjectiveDegreeZeroEquiv, MvPolynomial.map_C, map_one]

/-- The actual projective coefficient morphism is a morphism over
the given coefficient-ring map, with the original degree-zero base identifications. -/
theorem polynomialProjectiveCoefficientMap_to_base :
    polynomialProjectiveCoefficientMap f ≫ polynomialProjectiveToBase C =
      polynomialProjectiveToBase E ≫ Spec.map (CommRingCat.ofHom f) := by
  unfold polynomialProjectiveCoefficientMap polynomialProjectiveToBase
  apply (Proj.mapAffineOpenCover (polynomialCoefficientGradedHom f)
    (polynomialCoefficientGradedHom_irrelevant_le f)).openCover.hom_ext
  intro i
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  rw [Proj.awayι_comp_map_assoc (polynomialCoefficientGradedHom f)
    (polynomialCoefficientGradedHom_irrelevant_le f) i.1.2 i.2 i.2.2]
  simp only [Category.assoc, Proj.awayι_toSpecZero_assoc,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact polynomialCoefficientAwayMap_base_constant f i.2 c

end DimensionFourDependence
