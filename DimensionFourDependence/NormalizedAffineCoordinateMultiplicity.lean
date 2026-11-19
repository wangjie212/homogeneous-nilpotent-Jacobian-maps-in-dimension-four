import DimensionFourDependence.AffineCoordinateMultiplicity
import DimensionFourDependence.NormalizationRing

/-! # The coordinate multiplicity bound on the canonical finite normalization

The local ring is the actual height-one localization of the integral
closure in the original affine fraction field. Its normality, finiteness,
birational field actions and source-center identification are constructed.
-/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {k A : Type u} [Field k] [CharZero k]
  [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]

/-- Every height-one prime of the canonical normalization satisfies the
original hypersurface-degree bound for a nonzero original coordinate.
No abstract normal local model or projection data are supplied. -/
theorem canonical_normalization_coordinate_order_le_totalDegree
    (x : Option (Option Unit) → A) (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (htr : 2 ≤ Algebra.trdeg k A)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1)
    (hz0 : x (some none) ≠ 0)
    (hz : algebraMap A (normalizationRing A) (x (some none)) ∈ Q)
    (f : MvPolynomial (Option (Option Unit)) k) (hf : f ≠ 0)
    (hroot : MvPolynomial.aeval x f = 0)
    (a : ℕ) (horder : algebraMap A (Localization.AtPrime Q) (x (some none)) ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a) :
    a ≤ f.totalDegree := by
  let S := normalizationRing A
  let B := Localization.AtPrime Q
  let L := FractionRing A
  let : FaithfulSMul A S := inferInstance
  let : IsScalarTower k A S := inferInstance
  let : IsScalarTower k A B := inferInstance
  let : IsScalarTower A S B := inferInstance
  let : IsScalarTower k A L := inferInstance
  let : Module.Finite A S := normalizationRing_finite A (K := k)
  let : Algebra.IsIntegral A S := inferInstance
  let : Algebra.FiniteType k S :=
    (inferInstance : Algebra.FiniteType k A).trans (inferInstance : Algebra.FiniteType A S)
  let : IsIntegrallyClosed S := normalizationRing_isIntegrallyClosed A
  let : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization B Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  let : IsFractionRing S L := normalizationRing_isFractionRing A
  let : Algebra B L := IsLocalization.localizationAlgebraOfSubmonoidLe B L
    Q.primeCompl (nonZeroDivisors S) Q.primeCompl_le_nonZeroDivisors
  let : IsScalarTower S B L := IsLocalization.localization_isScalarTower_of_submonoid_le B L
    Q.primeCompl (nonZeroDivisors S) Q.primeCompl_le_nonZeroDivisors
  let : IsFractionRing B L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl B L
  let : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq (fun c =>
    (IsScalarTower.algebraMap_apply A S L c).trans
      ((IsScalarTower.algebraMap_apply S B L (algebraMap A S c)).trans
        (congrArg (algebraMap B L) (IsScalarTower.algebraMap_apply A S B c).symm)))
  let : IsScalarTower k B L := IsScalarTower.of_algebraMap_eq (fun c =>
    (IsScalarTower.algebraMap_apply k A L c).trans
      ((IsScalarTower.algebraMap_apply A B L (algebraMap k A c)).trans
        (congrArg (algebraMap B L) (IsScalarTower.algebraMap_apply k A B c).symm)))
  have hcenter : ((IsLocalRing.maximalIdeal B).under S).height = 1 := by
    change ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).under (normalizationRing A)).height = 1
    rw [Localization.AtPrime.under_maximalIdeal]
    exact hQ
  have hz' : algebraMap A B (x (some none)) ∈ IsLocalRing.maximalIdeal B := by
    rw [IsScalarTower.algebraMap_apply A S B]
    change algebraMap A S (x (some none)) ∈ (IsLocalRing.maximalIdeal B).under S
    rwa [Localization.AtPrime.under_maximalIdeal]
  exact @affine_hypersurface_normalization_coordinate_order_le_totalDegree k A S B L
    (inferInstance : Field k)
    (inferInstance : CharZero k)
    (inferInstance : CommRing A)
    (inferInstance : IsDomain A)
    (inferInstance : Algebra k A)
    (inferInstance : CommRing S)
    (inferInstance : IsDomain S)
    (inferInstance : Algebra k S)
    (inferInstance : Algebra.FiniteType k S)
    (inferInstance : Algebra A S)
    (inferInstance : FaithfulSMul A S)
    (inferInstance : Algebra.IsIntegral A S)
    (inferInstance : IsScalarTower k A S)
    (inferInstance : CommRing B)
    (inferInstance : IsDomain B)
    (inferInstance : IsLocalRing B)
    (inferInstance : IsIntegrallyClosed B)
    (inferInstance : Algebra k B)
    (inferInstance : Algebra A B)
    (inferInstance : Algebra S B)
    (inferInstance : IsScalarTower k A B)
    (inferInstance : IsScalarTower A S B)
    (inferInstance : Field L)
    (inferInstance : Algebra k L)
    (inferInstance : Algebra A L)
    (inferInstance : Algebra B L)
    (inferInstance : IsFractionRing A L)
    (inferInstance : IsFractionRing B L)
    (inferInstance : IsScalarTower k A L)
    (inferInstance : IsScalarTower k B L)
    (inferInstance : IsScalarTower A B L)
    x hx htr hcenter hz0 hz' f hf hroot a horder

end DimensionFourDependence
