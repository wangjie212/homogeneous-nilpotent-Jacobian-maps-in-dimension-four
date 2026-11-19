import DimensionFourDependence.SourceDenominatorPrime
import DimensionFourDependence.SourcePrimeLocalExtension
import DimensionFourDependence.UnramifiedDivisorOrder
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr

/-! # A given normalization prime has an unramified source-DVR model

The normal source-denominator model is finite étale over the source DVR.
Starting with a normalization prime over the original source divisor,
we construct its extended prime in that model, prove contraction to the
source local maximal ideal, and identify the two prime local rings.
-/

namespace DimensionFourDependence

variable {R S O B F : Type*} [CommRing R] [CommRing S]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing B] [IsDedekindDomain B] [Field F]
  [Algebra R S] [Algebra R O] [Algebra R B]
  [Algebra S B] [Algebra O B] [IsScalarTower R S B] [IsScalarTower R O B]
  [Algebra S F] [Algebra B F] [IsScalarTower S B F] [IsFractionRing B F]
  [Algebra.Etale O B]

/-- The complete prime-local model statement, retaining the actual
normalization map and the given normalization prime. -/
noncomputable def NormalizedPrimeUnramifiedSourceModel
    (Q : Ideal R) [Q.IsPrime] : Prop :=
  letI : Algebra R (integralClosure S F) :=
    ((algebraMap S (integralClosure S F)).comp (algebraMap R S)).toAlgebra
  ∀ (q : Ideal (integralClosure S F)) [q.IsPrime] [q.LiesOver Q],
    letI : Algebra (integralClosure S F) B :=
      (integralClosureToNormalLocalHom (S := S) (A := B) (F := F)).toRingHom.toAlgebra
    let P := q.map (algebraMap (integralClosure S F) B)
    ∃ hP : P.IsPrime,
      P.LiesOver (IsLocalRing.maximalIdeal O) ∧
      @IsDiscreteValuationRing (@Localization.AtPrime B _ P hP) _ _ ∧
      Algebra.IsUnramifiedAt O P ∧
      @Nonempty (Localization.AtPrime q ≃ₐ[integralClosure S F] @Localization.AtPrime B _ P hP)

/-- A given normalization prime over the source divisor is explicitly
identified with an unramified DVR in the normal finite étale source model. -/
theorem normalized_prime_unramified_source_model
    (Q : Ideal R) [Q.IsPrime] [IsLocalization.AtPrime O Q]
    [IsLocalization (Algebra.algebraMapSubmonoid S Q.primeCompl) B] :
    NormalizedPrimeUnramifiedSourceModel (S := S) (O := O) (B := B) (F := F) Q := by
  let : Algebra R (integralClosure S F) :=
    ((algebraMap S (integralClosure S F)).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S (integralClosure S F) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  intro q hq hlie
  let : Algebra (integralClosure S F) B :=
    (integralClosureToNormalLocalHom (S := S) (A := B) (F := F)).toRingHom.toAlgebra
  let : IsScalarTower S (integralClosure S F) B := IsScalarTower.of_algebraMap_eq
    (fun s => ((integralClosureToNormalLocalHom (S := S) (A := B) (F := F)).commutes s).symm)
  let : IsScalarTower R (integralClosure S F) B :=
    IsScalarTower.to₁₃₄ R S (integralClosure S F) B
  let M := Algebra.algebraMapSubmonoid (integralClosure S F)
    (Algebra.algebraMapSubmonoid S Q.primeCompl)
  let : IsLocalization M B :=
    integralClosure_normal_denominator_localization (Algebra.algebraMapSubmonoid S Q.primeCompl)
  have hM : Disjoint (M : Set (integralClosure S F)) (q : Set (integralClosure S F)) :=
    source_denominators_disjoint_of_liesOver (S := S) Q q
  let P := q.map (algebraMap (integralClosure S F) B)
  let hP : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M B q inferInstance hM
  let : P.IsPrime := hP
  have hunder : P.under (integralClosure S F) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M B inferInstance hM
  let : P.LiesOver Q := ⟨by
    rw [← Ideal.under_under (B := integralClosure S F), hunder]
    exact Ideal.over_def q Q⟩
  let : P.LiesOver (IsLocalRing.maximalIdeal O) := source_prime_liesOver_local_maximalIdeal Q P
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field O) P
  refine ⟨hP, inferInstance,
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hPne _,
    inferInstance, ?_⟩
  exact ⟨normalizedPrimeNormalSourceLocalEquiv
    (A := B) (Algebra.algebraMapSubmonoid S Q.primeCompl) q hM⟩

end DimensionFourDependence
