import DimensionFourDependence.LocalizationDerivationFieldCompatibility
import DimensionFourDependence.PrimeLocalizationFunctionField
import DimensionFourDependence.RationalPartial

/-! # Every original source coordinate derivative is regular on its prime localization -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] {n : ℕ}
  (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

/-- The actual base-linear coordinate derivative on the original
source prime localization, constructed by first-order localization. -/
noncomputable def primeLocalizationPartial (i : Fin n) :
    Derivation K (Localization.AtPrime Q) (Localization.AtPrime Q) :=
  localizationDerivation (S := Localization.AtPrime Q) Q.primeCompl (pderiv i)

/-- Original polynomial derivatives retain their exact values in the
local ring. -/
theorem primeLocalizationPartial_polynomial (i : Fin n) (P : MvPolynomial (Fin n) K) :
    primeLocalizationPartial Q i (algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime Q) P) =
      algebraMap (MvPolynomial (Fin n) K) (Localization.AtPrime Q) (pderiv i P) :=
  localizationDerivation_algebraMap Q.primeCompl (pderiv i) P

/-- The regular local derivative realizes the original rational partial
on every local element, rather than only on the polynomial generators. -/
theorem primeLocalizationPartial_compatible_source (i : Fin n) (v : Localization.AtPrime Q) :
    primeLocalizationFractionHom (F := FractionRing (MvPolynomial (Fin n) K)) Q (primeLocalizationPartial Q i v) =
      rationalPartial i (primeLocalizationFractionHom (F := FractionRing (MvPolynomial (Fin n) K)) Q v) :=
  localizationDerivation_compatible_field Q.primeCompl (pderiv i) (rationalPartial i)
    (primeLocalizationFractionHom (F := FractionRing (MvPolynomial (Fin n) K)) Q)
    (fun P => rationalPartial_polynomial i P) v

end DimensionFourDependence
