import DimensionFourDependence.Defs
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Flat.Basic

/-! # Coefficient extension of coordinate localizations

The actual tensor-product map induced by a coordinate localization is a
localization at the images of the same source denominators. Localizing it
at a prime gives the localization of the coefficient-extended coordinate
algebra at the contracted prime. No normality is needed for this step.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k S A E : Type*} [CommRing k] [CommRing S] [CommRing A] [CommRing E]
  [Algebra k S] [Algebra k A] [Algebra k E] [Algebra S A] [IsScalarTower k S A]

/-- The actual coefficient extension of a coordinate localization map. -/
noncomputable def coefficientLocalizationHom : S ⊗[k] E →ₐ[k] A ⊗[k] E :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom k S A) (AlgHom.id k E)

/-- The coefficient extension preserves the original coordinate map. -/
theorem coefficientLocalizationHom_tmul (s : S) (e : E) :
    coefficientLocalizationHom (k := k) (A := A) (s ⊗ₜ[k] e) =
      algebraMap S A s ⊗ₜ[k] e := rfl

/-- Flat coefficient extension preserves injectivity of the coordinate
localization map, as a map of the actual tensor product rings. -/
theorem coefficientLocalizationHom_injective [Module.Flat k E] [FaithfulSMul S A] :
    Function.Injective (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)) := by
  have hmap : (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toLinearMap =
      (IsScalarTower.toAlgHom k S A).toLinearMap.rTensor E := by
    ext s e
    rfl
  change Function.Injective (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toLinearMap
  rw [hmap]
  exact Module.Flat.rTensor_preserves_injective_linearMap _
    (FaithfulSMul.algebraMap_injective S A)

/-- Extending coefficients commutes with the given source denominator
localization, with the explicit tensor-product algebra map. -/
theorem coefficient_localization_isLocalization
    (M : Submonoid S) [IsLocalization M A] :
    letI : Algebra (S ⊗[k] E) (A ⊗[k] E) :=
      (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[k] E) M) (A ⊗[k] E) := by
  let : Algebra (S ⊗[k] E) (A ⊗[k] E) :=
    (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
  let : IsScalarTower S (S ⊗[k] E) (A ⊗[k] E) :=
    IsScalarTower.of_algebraMap_eq (by intro s; rfl)
  exact IsLocalization.tensorProduct_tensorProduct k E M A (by
    ext e
    change coefficientLocalizationHom (1 ⊗ₜ[k] e) = 1 ⊗ₜ[k] e
    rw [coefficientLocalizationHom_tmul, map_one])

/-- Localizing the extended source ring at a prime recovers the extended
coordinate algebra's local ring at the contraction of that prime. -/
theorem coefficient_localization_atPrime
    (M : Submonoid S) [IsLocalization M A] (Q : Ideal (A ⊗[k] E)) [Q.IsPrime] :
    letI : Algebra (S ⊗[k] E) (A ⊗[k] E) :=
      (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
    IsLocalization.AtPrime (Localization.AtPrime Q) (Q.under (S ⊗[k] E)) := by
  let : Algebra (S ⊗[k] E) (A ⊗[k] E) :=
    (coefficientLocalizationHom (k := k) (S := S) (A := A) (E := E)).toRingHom.toAlgebra
  let : IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[k] E) M) (A ⊗[k] E) :=
    coefficient_localization_isLocalization M
  exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (Algebra.algebraMapSubmonoid (S ⊗[k] E) M) (Localization.AtPrime Q) Q

end DimensionFourDependence
