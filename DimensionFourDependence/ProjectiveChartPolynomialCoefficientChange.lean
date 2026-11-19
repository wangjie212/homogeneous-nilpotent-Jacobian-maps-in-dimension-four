import DimensionFourDependence.ProjectiveChartPolynomialSections

/-! # Actual projective polynomial sections preserve original coefficient change -/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 1000000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C E : Type u} [Field C] [Field E] (φ : C →+* E)

local notation "U₀" a:max => Proj.basicOpen (homogeneousSubmodule (Fin 4) C) (X a)
local notation "U₁" a:max => Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X a)
local notation "g" => polynomialProjectiveCoefficientMap φ
local notation "hg" a:max => le_of_eq (polynomialProjectiveCoefficientMap_preimage_basicOpen φ a).symm

/-- The actual coefficient morphism pulls every original regular
chart constant back to the same constant with its mapped coefficient. -/
theorem polynomialProjectiveCoefficientMap_constantSection (a : Fin 4) (c : C) :
    (g).appLE (U₀ a) (U₁ a) (hg a) (projectiveConstantSectionHom C (U₀ a) c) =
      projectiveConstantSectionHom E (U₁ a) (φ c) := by
  let v := Away.mk (homogeneousSubmodule (Fin 4) C) (isHomogeneous_X (R := C) a) 0
    (MvPolynomial.C c) (isHomogeneous_C (Fin 4) c)
  have h := ConcreteCategory.congr_hom (polynomialProjectiveCoefficientMap_awayToSection φ a) v
  change (g).appLE (U₀ a) (U₁ a) (hg a)
      ((Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) C) (X a)
        (isHomogeneous_X (R := C) a) (by omega)).hom v) =
    (Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) E) (X a)
      (isHomogeneous_X (R := E) a) (by omega)).hom (polynomialCoefficientAwayHom φ a v) at h
  rw [projectiveConstantSectionHom_awayToSection, projectiveConstantSectionHom_awayToSection]
  simpa only [v, polynomialCoefficientAwayHom_mk, MvPolynomial.map_C] using h

/-- The actual coefficient morphism fixes every original regular
coordinate-ratio section. -/
theorem polynomialProjectiveCoefficientMap_coordinateRatioSection (a i : Fin 4) :
    (g).appLE (U₀ a) (U₁ a) (hg a) (projectiveCoordinateRatioSection C a i) =
      projectiveCoordinateRatioSection E a i := by
  let v := Away.mk (homogeneousSubmodule (Fin 4) C) (isHomogeneous_X (R := C) a) 1
    (X i : MvPolynomial (Fin 4) C) (by simpa using isHomogeneous_X (R := C) i)
  have h := ConcreteCategory.congr_hom (polynomialProjectiveCoefficientMap_awayToSection φ a) v
  change (g).appLE (U₀ a) (U₁ a) (hg a)
      ((Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) C) (X a)
        (isHomogeneous_X (R := C) a) (by omega)).hom v) =
    (Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) E) (X a)
      (isHomogeneous_X (R := E) a) (by omega)).hom (polynomialCoefficientAwayHom φ a v) at h
  rw [projectiveCoordinateRatioSection_awayToSection, projectiveCoordinateRatioSection_awayToSection]
  simpa only [v, polynomialCoefficientAwayHom_mk, MvPolynomial.map_X] using h

/-- Every actual original chart-polynomial section pulls back by
mapping only its original coefficients and retaining its source coordinates. -/
theorem polynomialProjectiveCoefficientMap_chartPolynomialSection
    (a : Fin 4) (P : MvPolynomial (Fin 4) C) :
    (g).appLE (U₀ a) (U₁ a) (hg a) (projectiveChartPolynomialSectionHom C a P) =
      projectiveChartPolynomialSectionHom E a (MvPolynomial.map φ P) := by
  have heq : ((g).appLE (U₀ a) (U₁ a) (hg a)).hom.comp
      (projectiveChartPolynomialSectionHom C a) =
        (projectiveChartPolynomialSectionHom E a).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, projectiveChartPolynomialSectionHom,
        eval₂Hom_C, MvPolynomial.map_C]
      exact polynomialProjectiveCoefficientMap_constantSection φ a c
    · intro i
      simp only [RingHom.comp_apply, projectiveChartPolynomialSectionHom,
        eval₂Hom_X', MvPolynomial.map_X]
      exact polynomialProjectiveCoefficientMap_coordinateRatioSection φ a i
  exact RingHom.congr_fun heq P

end DimensionFourDependence
