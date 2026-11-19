import DimensionFourDependence.ProjectiveCoefficientMorphism
import DimensionFourDependence.HomogeneousChartEvaluation

/-! # Coefficient extension preserves the actual projective chart fractions

The coefficient morphism on Proj pulls back an original homogeneous
fraction by mapping its numerator coefficients and retaining the same
original coordinate denominator. This is a statement about the actual
global morphism's map on affine sections.
-/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C E : Type u} [CommRing C] [CommRing E] (f : C →+* E)

local notation "𝒢C" => homogeneousSubmodule (Fin 4) C
local notation "𝒢E" => homogeneousSubmodule (Fin 4) E

/-- The graded coefficient map fixes every original source variable. -/
theorem polynomialCoefficientGradedHom_X (a : Fin 4) :
    polynomialCoefficientGradedHom f (X a) = X a := MvPolynomial.map_X f a

/-- Coefficient extension on the actual homogeneous localization,
with the same original coordinate as denominator on both sides. -/
noncomputable def polynomialCoefficientAwayHom (a : Fin 4) :
    Away 𝒢C (X a) →+* Away 𝒢E (X a) :=
  HomogeneousLocalization.map (polynomialCoefficientGradedHom f) (by
    rintro _ ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    change X a ^ n = MvPolynomial.map f (X a ^ n)
    simp only [map_pow, MvPolynomial.map_X])

/-- Actual original homogeneous fractions retain their denominator
coordinate and map only their numerator coefficients. -/
theorem polynomialCoefficientAwayHom_mk (a : Fin 4) (n : ℕ)
    (P : MvPolynomial (Fin 4) C) (hP : P ∈ 𝒢C (n • (1 : ℕ))) :
    polynomialCoefficientAwayHom f a
      (Away.mk 𝒢C (isHomogeneous_X (R := C) a) n P hP) =
      Away.mk 𝒢E (isHomogeneous_X (R := E) a) n (MvPolynomial.map f P) (hP.map f) := by
  apply HomogeneousLocalization.val_injective
  simp only [polynomialCoefficientAwayHom, Away.mk, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk]
  change Localization.mk (MvPolynomial.map f P)
    ⟨MvPolynomial.map f (X a ^ n), _⟩ =
      Localization.mk (MvPolynomial.map f P) ⟨X a ^ n, _⟩
  simp only [map_pow, MvPolynomial.map_X]

/-- The actual global coefficient morphism's map on projective chart
sections is precisely the specified original homogeneous-fraction map. -/
theorem polynomialProjectiveCoefficientMap_awayToSection (a : Fin 4) :
    Proj.awayToSection 𝒢C (X a) ≫
      (polynomialProjectiveCoefficientMap f).appLE
        (Proj.basicOpen 𝒢C (X a)) (Proj.basicOpen 𝒢E (X a))
        (le_of_eq (polynomialProjectiveCoefficientMap_preimage_basicOpen f a).symm) =
      CommRingCat.ofHom (polynomialCoefficientAwayHom f a) ≫ Proj.awayToSection 𝒢E (X a) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro w
  obtain ⟨n, P, hP, rfl⟩ := Away.mk_surjective 𝒢C (isHomogeneous_X (R := C) a) w
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    polynomialCoefficientAwayHom_mk]
  refine Subtype.ext (funext fun p => ?_)
  change HomogeneousLocalization.mk _ = HomogeneousLocalization.mk _
  ext
  simp [polynomialCoefficientGradedHom, polynomialProjectiveCoefficientMap]

end DimensionFourDependence
