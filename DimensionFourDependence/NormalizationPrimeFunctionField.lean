import DimensionFourDependence.NormalizationRing
import DimensionFourDependence.PrimeLocalizationFunctionField

/-! # The actual normalization prime in the original function field

The prime localization of the canonical normalization embeds into the
original affine fraction field. This fixes the local-ring action and all
original coordinate and constant-field actions without auxiliary choices.
-/

namespace DimensionFourDependence

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The actual normalization-prime localization acts on the original
affine fraction field through its canonical birational inclusion. -/
@[instance_reducible]
noncomputable def normalizationPrimeFractionAlgebra
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] :
    Algebra (Localization.AtPrime Q) (FractionRing A) := by
  let : IsFractionRing (normalizationRing A) (FractionRing A) := normalizationRing_isFractionRing A
  let : FaithfulSMul (normalizationRing A) (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (normalizationRing A) (FractionRing A))
  exact primeLocalizationFractionAlgebra Q

/-- The actual local inclusion preserves every original affine coordinate. -/
theorem normalizationPrimeFractionAlgebra_source_scalarTower
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] :
    let : Algebra (Localization.AtPrime Q) (FractionRing A) := normalizationPrimeFractionAlgebra Q
    IsScalarTower A (Localization.AtPrime Q) (FractionRing A) := by
  let : IsFractionRing (normalizationRing A) (FractionRing A) := normalizationRing_isFractionRing A
  let : FaithfulSMul (normalizationRing A) (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (normalizationRing A) (FractionRing A))
  exact primeLocalizationFraction_base_scalarTower Q

/-- The original affine function field is the fraction field of the
actual normalization-prime local ring. -/
theorem normalizationPrimeFractionAlgebra_isFractionRing
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] :
    let : Algebra (Localization.AtPrime Q) (FractionRing A) := normalizationPrimeFractionAlgebra Q
    IsFractionRing (Localization.AtPrime Q) (FractionRing A) := by
  let : IsFractionRing (normalizationRing A) (FractionRing A) := normalizationRing_isFractionRing A
  let : FaithfulSMul (normalizationRing A) (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (normalizationRing A) (FractionRing A))
  exact primeLocalizationFraction_isFractionRing Q

variable {k : Type*} [CommRing k] [Algebra k A]

/-- The actual normalization-prime inclusion preserves the entire
original constant-ring action. -/
theorem normalizationPrimeFractionAlgebra_base_scalarTower
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] :
    let : Algebra (Localization.AtPrime Q) (FractionRing A) := normalizationPrimeFractionAlgebra Q
    IsScalarTower k (Localization.AtPrime Q) (FractionRing A) := by
  let : Algebra (Localization.AtPrime Q) (FractionRing A) := normalizationPrimeFractionAlgebra Q
  let : IsScalarTower A (Localization.AtPrime Q) (FractionRing A) :=
    normalizationPrimeFractionAlgebra_source_scalarTower Q
  exact IsScalarTower.to₁₃₄ k A (Localization.AtPrime Q) (FractionRing A)

end DimensionFourDependence
