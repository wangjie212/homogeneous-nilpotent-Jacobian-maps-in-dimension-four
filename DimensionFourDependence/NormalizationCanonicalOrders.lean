import DimensionFourDependence.NormalizationLocalSourceOrders
import DimensionFourDependence.CanonicalSourceLocalMap

/-! # Canonical local-ring orders from the constructed normalization model

The normal source model supplies exact order comparisons for the actual
canonical map from the source prime localization. The normal model and
its auxiliary extended prime do not occur in the regular-order conclusion.
-/

namespace DimensionFourDependence

variable {R S B F L : Type*} [CommRing R] [IsDomain R] [CommRing S]
  [CommRing B] [IsDedekindDomain B] [Field F] [Field L]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  [Algebra S F] [Algebra B F] [IsScalarTower S B F] [IsFractionRing B F]
  (Q : Ideal R) [Q.IsPrime]
  [IsDiscreteValuationRing (Localization.AtPrime Q)]
  [Algebra (Localization.AtPrime Q) B] [IsScalarTower R (Localization.AtPrime Q) B]
  [Algebra.Etale (Localization.AtPrime Q) B]
  [Algebra (Localization.AtPrime Q) L] [IsFractionRing (Localization.AtPrime Q) L]

omit [IsScalarTower R S B] in
/-- The full normalization source model implies exact regular order
bounds for the canonical local-ring map at every given normalization prime. -/
theorem normalization_local_canonical_regular_orders
    (hmodel : NormalizationLocalSourceOrders (S := S) (O := Localization.AtPrime Q)
      (B := B) (F := F) (L := L) Q) :
    letI : Algebra R (integralClosure S F) :=
      ((algebraMap S (integralClosure S F)).comp (algebraMap R S)).toAlgebra
    ∀ (q : Ideal (integralClosure S F)) [q.IsPrime] [q.LiesOver Q]
      (x : Localization.AtPrime Q) (a : ℕ),
      Localization.localRingHom Q q (algebraMap R (integralClosure S F)) (Ideal.over_def q Q) x ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a ↔
          x ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a := by
  let : Algebra R (integralClosure S F) :=
    ((algebraMap S (integralClosure S F)).comp (algebraMap R S)).toAlgebra
  intro q hq hlie x a
  let : Algebra (integralClosure S F) B :=
    (integralClosureToNormalLocalHom (S := S) (A := B) (F := F)).toRingHom.toAlgebra
  let P := q.map (algebraMap (integralClosure S F) B)
  obtain ⟨hP, hPlie, e, _, _, horders, _⟩ := @hmodel q hq hlie
  let : P.IsPrime := hP
  let : P.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) := hPlie
  have heq := localEquivSourceAlgHom_eq_canonical_localRingHom Q q e
  rw [← heq]
  exact horders x a

omit [IsScalarTower R S B] in
/-- Every actual normalized prime has a rational pullback extending
the canonical source-local map and preserving all normalized orders. -/
theorem normalization_local_canonical_rational_orders
    (hmodel : NormalizationLocalSourceOrders (S := S) (O := Localization.AtPrime Q)
      (B := B) (F := F) (L := L) Q) :
    letI : Algebra R (integralClosure S F) :=
      ((algebraMap S (integralClosure S F)).comp (algebraMap R S)).toAlgebra
    ∀ (q : Ideal (integralClosure S F)) [q.IsPrime] [q.LiesOver Q],
      ∃ hdvr : IsDiscreteValuationRing (Localization.AtPrime q),
        letI := hdvr
        letI : Algebra (Localization.AtPrime q) (FractionRing (Localization.AtPrime q)) :=
          OreLocalization.instAlgebra
        ∃ j : L →+* FractionRing (Localization.AtPrime q),
          (∀ x : Localization.AtPrime Q,
            j (algebraMap (Localization.AtPrime Q) L x) =
              algebraMap (Localization.AtPrime q) (FractionRing (Localization.AtPrime q))
                (Localization.localRingHom Q q (algebraMap R (integralClosure S F))
                  (Ideal.over_def q Q) x)) ∧
          let v : IsDedekindDomain.HeightOneSpectrum (Localization.AtPrime Q) :=
            ⟨IsLocalRing.maximalIdeal _, inferInstance, IsDiscreteValuationRing.not_a_field _⟩
          let w : IsDedekindDomain.HeightOneSpectrum (Localization.AtPrime q) :=
            ⟨IsLocalRing.maximalIdeal _, inferInstance, IsDiscreteValuationRing.not_a_field _⟩
          ∀ x : L, v.valuation L x = w.valuation (FractionRing (Localization.AtPrime q)) (j x) := by
  let : Algebra R (integralClosure S F) :=
    ((algebraMap S (integralClosure S F)).comp (algebraMap R S)).toAlgebra
  intro q hq hlie
  let : Algebra (integralClosure S F) B :=
    (integralClosureToNormalLocalHom (S := S) (A := B) (F := F)).toRingHom.toAlgebra
  let P := q.map (algebraMap (integralClosure S F) B)
  obtain ⟨hP, hPlie, e, hdvr, _, _, _⟩ := @hmodel q hq hlie
  let : P.IsPrime := hP
  let : P.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) := hPlie
  have hdata := etale_divisor_local_source_properties (O := Localization.AtPrime Q) P
  let : IsDiscreteValuationRing (Localization.AtPrime P) := hdata.1
  let : Module.IsTorsionFree (Localization.AtPrime Q) (Localization.AtPrime P) := hdata.2.1
  let : Algebra.EssFiniteType (Localization.AtPrime Q) (Localization.AtPrime P) := hdata.2.2.1
  let : Algebra.FormallyUnramified (Localization.AtPrime Q) (Localization.AtPrime P) := hdata.2.2.2.1
  let : IsLocalHom (algebraMap (Localization.AtPrime Q) (Localization.AtPrime P)) := hdata.2.2.2.2
  let : IsScalarTower R (Localization.AtPrime Q) (Localization.AtPrime P) :=
    IsScalarTower.to₁₂₄ R (Localization.AtPrime Q) B (Localization.AtPrime P)
  exact ⟨hdvr, canonical_localRingHom_rational_order (F := L) Q q e⟩

end DimensionFourDependence
