import DimensionFourDependence.NormalCoordinateLocalization
import DimensionFourDependence.DenominatorPrimeLocalRing

/-! # A given normalization prime in the already normal source model

When source-denominator localization is normal, a prime of the original
coordinate normalization that avoids those denominators extends to the
normal source model. Its local ring is explicitly identified with the
local ring at that extended prime. No upstairs local-ring identity is
assumed.
-/

namespace DimensionFourDependence

variable {S A F : Type*} [CommRing S] [CommRing A] [Field F]
  [Algebra S A] [Algebra S F] [Algebra A F] [IsScalarTower S A F]
  [IsFractionRing A F] [IsIntegrallyClosed A]

/-- The explicit local-ring identification for a given normalization
prime surviving in the already normal source denominator model. -/
noncomputable def normalizedPrimeNormalSourceLocalEquiv
    (M : Submonoid S) [IsLocalization M A]
    (q : Ideal (integralClosure S F)) [q.IsPrime]
    (hM : Disjoint (Algebra.algebraMapSubmonoid (integralClosure S F) M : Set (integralClosure S F))
      (q : Set (integralClosure S F))) :
    letI : Algebra (integralClosure S F) A :=
      (integralClosureToNormalLocalHom (S := S) (A := A) (F := F)).toRingHom.toAlgebra
    letI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure S F) M) A :=
      integralClosure_normal_denominator_localization M
    let P := q.map (algebraMap (integralClosure S F) A)
    letI : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid (integralClosure S F) M) A q inferInstance hM
    Localization.AtPrime q ≃ₐ[integralClosure S F] Localization.AtPrime P := by
  let : Algebra (integralClosure S F) A :=
    (integralClosureToNormalLocalHom (S := S) (A := A) (F := F)).toRingHom.toAlgebra
  let : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure S F) M) A :=
    integralClosure_normal_denominator_localization M
  exact denominatorPrimeLocalEquiv (A := A) (Algebra.algebraMapSubmonoid (integralClosure S F) M) q hM

end DimensionFourDependence
