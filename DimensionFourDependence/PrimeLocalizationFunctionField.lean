import DimensionFourDependence.Defs
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Source divisor localizations in a chosen actual function field

A prime localization embeds canonically into any given field containing
the source domain. When that field is the source fraction field, it is
also the fraction field of the prime localization. The explicit maps
retain all coefficient and source scalar towers.
-/

namespace DimensionFourDependence

variable {R F : Type*} [CommRing R] [Field F]
  [Algebra R F] [FaithfulSMul R F]

/-- The source prime localization maps to the chosen containing field
through its original source inclusion. -/
noncomputable def primeLocalizationFractionHom (Q : Ideal R) [Q.IsPrime] :
    Localization.AtPrime Q →ₐ[R] F :=
  IsLocalization.liftAlgHom (M := Q.primeCompl) (f := Algebra.ofId R F) fun s => by
    apply isUnit_iff_ne_zero.mpr
    intro hs
    have hz : (s : R) = 0 := FaithfulSMul.algebraMap_injective R F (by simpa using hs)
    exact s.property (hz ▸ Q.zero_mem)

/-- The localization map agrees with the original source map. -/
theorem primeLocalizationFractionHom_algebraMap (Q : Ideal R) [Q.IsPrime] (r : R) :
    primeLocalizationFractionHom (F := F) Q (algebraMap R (Localization.AtPrime Q) r) =
      algebraMap R F r :=
  IsLocalization.lift_eq _ _

/-- The chosen source-field action of the prime localization. -/
@[instance_reducible]
noncomputable def primeLocalizationFractionAlgebra (Q : Ideal R) [Q.IsPrime] :
    Algebra (Localization.AtPrime Q) F := (primeLocalizationFractionHom Q).toRingHom.toAlgebra

/-- The chosen containing-field map preserves the original source
localization scalar tower. -/
theorem primeLocalizationFraction_scalarTower (Q : Ideal R) [Q.IsPrime] :
    letI : Algebra (Localization.AtPrime Q) F := primeLocalizationFractionAlgebra Q
    IsScalarTower R (Localization.AtPrime Q) F := by
  let : Algebra (Localization.AtPrime Q) F := primeLocalizationFractionAlgebra Q
  exact IsScalarTower.of_algebraMap_eq
    (fun r => (primeLocalizationFractionHom_algebraMap Q r).symm)

/-- Prime localization preserves the chosen actual source fraction field. -/
theorem primeLocalizationFraction_isFractionRing [IsDomain R] (Q : Ideal R) [Q.IsPrime] [IsFractionRing R F] :
    letI : Algebra (Localization.AtPrime Q) F := primeLocalizationFractionAlgebra Q
    IsFractionRing (Localization.AtPrime Q) F := by
  let : Algebra (Localization.AtPrime Q) F := primeLocalizationFractionAlgebra Q
  let : IsScalarTower R (Localization.AtPrime Q) F := primeLocalizationFraction_scalarTower Q
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl (Localization.AtPrime Q) F

variable {K : Type*} [CommRing K] [Algebra K R] [Algebra K F] [IsScalarTower K R F]

/-- The chosen prime-local source map also preserves the original
coefficient field action. -/
theorem primeLocalizationFraction_base_scalarTower (Q : Ideal R) [Q.IsPrime] :
    letI : Algebra (Localization.AtPrime Q) F := primeLocalizationFractionAlgebra Q
    IsScalarTower K (Localization.AtPrime Q) F := by
  let : Algebra (Localization.AtPrime Q) F := primeLocalizationFractionAlgebra Q
  let : IsScalarTower R (Localization.AtPrime Q) F := primeLocalizationFraction_scalarTower Q
  exact IsScalarTower.to₁₃₄ K R (Localization.AtPrime Q) F

end DimensionFourDependence
