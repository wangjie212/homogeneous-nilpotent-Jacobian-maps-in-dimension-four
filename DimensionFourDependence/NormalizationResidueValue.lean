import DimensionFourDependence.NormalizationResidueCoordinateField

/-! # The original normalization residue-coordinate action retains every original source value -/

namespace DimensionFourDependence

variable {A : Type*} [CommRing A]

/-- The named actual residue-coordinate action agrees with the
canonical path through the same normalization and prime quotient. -/
theorem normalizationPrimeResidueCoordinateAlgebra_value
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (a : A) :
    letI : Field (FractionRing (normalizationRing A ⧸ Q)) := normalizationPrimeResidueFieldInstance Q
    letI : Algebra A (FractionRing (normalizationRing A ⧸ Q)) := normalizationPrimeResidueCoordinateAlgebra Q
    algebraMap (normalizationRing A) (FractionRing (normalizationRing A ⧸ Q))
      (algebraMap A (normalizationRing A) a) =
        algebraMap A (FractionRing (normalizationRing A ⧸ Q)) a := by
  letI : Field (FractionRing (normalizationRing A ⧸ Q)) := normalizationPrimeResidueFieldInstance Q
  letI : Algebra A (FractionRing (normalizationRing A ⧸ Q)) := normalizationPrimeResidueCoordinateAlgebra Q
  exact (IsScalarTower.algebraMap_apply A (normalizationRing A)
    (FractionRing (normalizationRing A ⧸ Q)) a).symm

end DimensionFourDependence
