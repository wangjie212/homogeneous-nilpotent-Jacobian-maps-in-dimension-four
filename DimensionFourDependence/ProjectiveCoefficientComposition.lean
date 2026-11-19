import DimensionFourDependence.ProjectiveCoefficientMorphism

/-! # Actual projective coefficient projections compose -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {C E F : Type u} [CommRing C] [CommRing E] [CommRing F]
  (f : C →+* E) (g : E →+* F)

/-- Mapping polynomial coefficients through a tower gives exactly
the composite of the two actual graded polynomial homomorphisms. -/
theorem polynomialCoefficientGradedHom_comp :
    polynomialCoefficientGradedHom (g.comp f) =
      (polynomialCoefficientGradedHom g).comp (polynomialCoefficientGradedHom f) := by
  ext P : 1
  exact (MvPolynomial.map_map f g P).symm

/-- The actual projective coefficient projections compose in the
original source-coordinate order. -/
theorem polynomialProjectiveCoefficientMap_comp :
    polynomialProjectiveCoefficientMap (g.comp f) =
      polynomialProjectiveCoefficientMap g ≫ polynomialProjectiveCoefficientMap f := by
  unfold polynomialProjectiveCoefficientMap
  simpa only [← polynomialCoefficientGradedHom_comp] using
    (Proj.map_comp (polynomialCoefficientGradedHom f) (polynomialCoefficientGradedHom g)
      (polynomialCoefficientGradedHom_irrelevant_le f) (polynomialCoefficientGradedHom_irrelevant_le g))

end DimensionFourDependence
