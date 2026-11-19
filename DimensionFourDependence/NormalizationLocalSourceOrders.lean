import DimensionFourDependence.NormalizedPrimeUnramifiedModel
import DimensionFourDependence.LocalEquivRationalOrder
import DimensionFourDependence.EtaleDivisorLocalProperties

/-! # Rational source orders at a given normalization prime

Starting with the given normalization prime over a source divisor, the
constructed local isomorphism preserves the original source ring. Its
inverse supplies the source DVR map into that normalization local ring.
Both regular vanishing bounds and all rational normalized orders agree.
-/

namespace DimensionFourDependence

variable {R S O B F L : Type*} [CommRing R] [CommRing S]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing B] [IsDedekindDomain B] [Field F] [Field L]
  [Algebra R S] [Algebra R O] [Algebra R B]
  [Algebra S B] [Algebra O B] [IsScalarTower R S B] [IsScalarTower R O B]
  [Algebra S F] [Algebra B F] [IsScalarTower S B F] [IsFractionRing B F]
  [Algebra.Etale O B] [Algebra O L] [IsFractionRing O L]

/-- The complete given-prime source-order comparison, retaining the
actual extended prime, its original-source local isomorphism, the source
function map, regular order bounds, and rational normalized valuations. -/
noncomputable def NormalizationLocalSourceOrders (Q : Ideal R) [Q.IsPrime] : Prop :=
  letI : Algebra R (integralClosure S F) :=
    ((algebraMap S (integralClosure S F)).comp (algebraMap R S)).toAlgebra
  ∀ (q : Ideal (integralClosure S F)) [q.IsPrime] [q.LiesOver Q],
    letI : Algebra (integralClosure S F) B :=
      (integralClosureToNormalLocalHom (S := S) (A := B) (F := F)).toRingHom.toAlgebra
    let P := q.map (algebraMap (integralClosure S F) B)
    ∃ hP : P.IsPrime,
      letI := hP
      ∃ hlie : P.LiesOver (IsLocalRing.maximalIdeal O),
        letI := hlie
        let hdata := etale_divisor_local_source_properties (O := O) P
        letI : IsDiscreteValuationRing (Localization.AtPrime P) := hdata.1
        letI : Module.IsTorsionFree O (Localization.AtPrime P) := hdata.2.1
        letI : Algebra.EssFiniteType O (Localization.AtPrime P) := hdata.2.2.1
        letI : Algebra.FormallyUnramified O (Localization.AtPrime P) := hdata.2.2.2.1
        letI : IsLocalHom (algebraMap O (Localization.AtPrime P)) := hdata.2.2.2.2
        letI : IsScalarTower R O (Localization.AtPrime P) :=
          IsScalarTower.to₁₂₄ R O B (Localization.AtPrime P)
        ∃ e : Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P,
          IsDiscreteValuationRing (Localization.AtPrime q) ∧
          (∀ r : R, localEquivSourceAlgHom (O := O) e (algebraMap R O r) =
            algebraMap R (Localization.AtPrime q) r) ∧
          (∀ (x : O) (a : ℕ), localEquivSourceAlgHom (O := O) e x ∈
            (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a ↔
              x ∈ (IsLocalRing.maximalIdeal O) ^ a) ∧
          LocalEquivSourceRationalOrder (O := O) (F := L) e

/-- Every given normalization prime over the source divisor has the
same regular and rational source orders in its actual local ring. -/
theorem normalization_local_source_orders
    (Q : Ideal R) [Q.IsPrime] [IsLocalization.AtPrime O Q]
    [IsLocalization (Algebra.algebraMapSubmonoid S Q.primeCompl) B] :
    NormalizationLocalSourceOrders (S := S) (O := O) (B := B) (F := F) (L := L) Q := by
  let : Algebra R (integralClosure S F) :=
    ((algebraMap S (integralClosure S F)).comp (algebraMap R S)).toAlgebra
  have hmodel := normalized_prime_unramified_source_model (S := S) (O := O) (B := B) (F := F) Q
  intro q hq hlie
  let : Algebra (integralClosure S F) B :=
    (integralClosureToNormalLocalHom (S := S) (A := B) (F := F)).toRingHom.toAlgebra
  obtain ⟨hP, hPlie, _, _, ⟨eN⟩⟩ := @hmodel q hq hlie
  let P := q.map (algebraMap (integralClosure S F) B)
  let : P.IsPrime := hP
  let : P.LiesOver (IsLocalRing.maximalIdeal O) := hPlie
  have hdata := etale_divisor_local_source_properties (O := O) P
  let : IsDiscreteValuationRing (Localization.AtPrime P) := hdata.1
  let : Module.IsTorsionFree O (Localization.AtPrime P) := hdata.2.1
  let : Algebra.EssFiniteType O (Localization.AtPrime P) := hdata.2.2.1
  let : Algebra.FormallyUnramified O (Localization.AtPrime P) := hdata.2.2.2.1
  let : IsLocalHom (algebraMap O (Localization.AtPrime P)) := hdata.2.2.2.2
  let : IsScalarTower R O (Localization.AtPrime P) := IsScalarTower.to₁₂₄ R O B (Localization.AtPrime P)
  let : IsScalarTower R S (integralClosure S F) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower S (integralClosure S F) B := IsScalarTower.of_algebraMap_eq
    (fun s => ((integralClosureToNormalLocalHom (S := S) (A := B) (F := F)).commutes s).symm)
  let : IsScalarTower R (integralClosure S F) B := IsScalarTower.to₁₃₄ R S (integralClosure S F) B
  let : IsScalarTower R (integralClosure S F) (Localization.AtPrime P) :=
    IsScalarTower.to₁₂₄ R (integralClosure S F) B (Localization.AtPrime P)
  let e : Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P := eN.restrictScalars R
  refine ⟨hP, hPlie, e, local_equiv_isDiscreteValuationRing e.toRingEquiv, ?_, ?_, ?_⟩
  · exact localEquivSourceAlgHom_original_source e
  · exact localEquivSource_maximalIdeal_pow_mem_iff (O := O) e
  · exact localEquivSource_rational_order (O := O) (F := L) e

end DimensionFourDependence
