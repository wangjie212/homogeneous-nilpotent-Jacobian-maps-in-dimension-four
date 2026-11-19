import DimensionFourDependence.CanonicalRationalOrderComparison
import DimensionFourDependence.CoefficientCanonicalRegularOrders

/-! # Named canonical rational orders on the coefficient normalization -/

namespace DimensionFourDependence

open scoped TensorProduct

variable {R k S F E : Type*} [CommRing R] [IsDomain R]
  [Field k] [CharZero k] [CommRing S] [Field F] [Field E]
  [Algebra R S] [Algebra k S] [Algebra k F] [Algebra k E]
  [Module.Finite k E]
  (Q : Ideal R) [Q.IsPrime]
  [IsDiscreteValuationRing (Localization.AtPrime Q)]
  [Algebra k (Localization.AtPrime Q)] [Algebra S (Localization.AtPrime Q)]
  [IsScalarTower R S (Localization.AtPrime Q)]
  [IsScalarTower k S (Localization.AtPrime Q)]
  [FaithfulSMul S (Localization.AtPrime Q)]
  [Algebra (Localization.AtPrime Q) F]
  [IsScalarTower k (Localization.AtPrime Q) F]
  [IsFractionRing (Localization.AtPrime Q) F]
  [IsLocalization (Algebra.algebraMapSubmonoid S Q.primeCompl) (Localization.AtPrime Q)]

local notation "O₀" => Localization.AtPrime Q
local notation "Sₑ" => S ⊗[k] E
local notation "Aₑ" => O₀ ⊗[k] E

/-- The canonical coefficient-normalization rational comparison in a
form that retains its local-map argument without expanding valuations. -/
theorem coefficient_canonical_rational_source_order_comparison
    (hclosed : algebraicClosure k F = ⊥) :
    letI : IsDomain Aₑ := relatively_closed_local_ring_base_change_isDomain hclosed
    letI : IsDomain Sₑ := Function.Injective.isDomain
      (coefficientLocalizationHom (k := k) (S := S) (A := O₀) (E := E)) coefficientLocalizationHom_injective
    letI : Algebra R Sₑ := sourceCoefficientExtensionAlgebra (R := R) (k := k) (S := S) (E := E)
    letI : Algebra R (normalizationRing Sₑ) :=
      ((algebraMap Sₑ (normalizationRing Sₑ)).comp (algebraMap R Sₑ)).toAlgebra
    ∀ (q : Ideal (normalizationRing Sₑ)) [q.IsPrime] [q.LiesOver Q],
      CanonicalRationalSourceOrderComparison (F := F)
        (Localization.localRingHom Q q (algebraMap R (normalizationRing Sₑ)) (Ideal.over_def q Q)) := by
  exact coefficient_canonical_normalization_rational_orders
    (R := R) (k := k) (S := S) (F := F) (E := E) Q hclosed

end DimensionFourDependence
