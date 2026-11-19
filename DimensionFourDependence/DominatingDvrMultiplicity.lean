import DimensionFourDependence.DvrNormalizationMultiplicity
import DimensionFourDependence.DedekindLocalOverring
import DimensionFourDependence.SourceLocalNormalization
import DimensionFourDependence.LocalEquivOrderTransport

/-! # The finite-degree bound on an actual dominating normal local ring

The actual target local ring constructs its own prime of the finite
source normalization. The resulting local isomorphism retains every
source value and transfers the uniformizer multiplicity bound to that
given ring. No independent normalization-prime model is a hypothesis.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {A B K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B]
  [Field K] [CharZero K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L]
  [Algebra A B] [Algebra A L] [Algebra B L] [IsFractionRing B L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [Module.Finite K L] [IsLocalHom (algebraMap A B)]

include K in
/-- An actual dominating normal local ring in a finite field extension
constructs its own normalization prime and original-source-compatible
local isomorphism. -/
theorem dominating_dvr_normalization_prime_model :
    ∃ q : PrimeSpectrum (integralClosure A L),
      q.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) ∧
        ∃ e : Localization.AtPrime q.asIdeal ≃+* B,
          ∀ a : A, e (algebraMap A (Localization.AtPrime q.asIdeal) a) = algebraMap A B a := by
  let S := integralClosure A L
  let : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr (by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K))
  let : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).mpr (IsFractionRing.injective B L)
  let : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain A K L S
  let : IsFractionRing S L := integralClosure.isFractionRing_of_finite_extension K L
  let g : S →ₐ[A] B := integralClosureToNormalLocalHom (S := A) (A := B) (F := L)
  let : Algebra S B := g.toRingHom.toAlgebra
  let : IsScalarTower A S B := IsScalarTower.of_algebraMap_eq (fun a => (g.commutes a).symm)
  let : IsScalarTower S B L := IsScalarTower.of_algebraMap_eq (fun s =>
    (integralClosureToNormalLocalHom_source (S := A) (A := B) (F := L) s).symm)
  let : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr (by
    intro x y hxy
    apply FaithfulSMul.algebraMap_injective A L
    exact congrArg Subtype.val hxy)
  let q : Ideal S := (IsLocalRing.maximalIdeal B).under S
  let : q.IsPrime := inferInstance
  have hlie : q.LiesOver (IsLocalRing.maximalIdeal A) := by
    apply (Ideal.liesOver_iff q (IsLocalRing.maximalIdeal A)).mpr
    change IsLocalRing.maximalIdeal A = ((IsLocalRing.maximalIdeal B).under S).under A
    rw [Ideal.under_under]
    exact (IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm
  let : q.LiesOver (IsLocalRing.maximalIdeal A) := hlie
  have hq0 : q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) q
  let e := dedekindLocalOverringEquiv (S := S) (B := B) L q rfl hq0
  refine ⟨⟨q, inferInstance⟩, hlie, e.toRingEquiv, ?_⟩
  intro a
  rw [IsScalarTower.algebraMap_apply A S (Localization.AtPrime q)]
  change e (algebraMap S (Localization.AtPrime q) (algebraMap A S a)) = algebraMap A B a
  rw [e.commutes, ← IsScalarTower.algebraMap_apply A S B]

/-- Every actual uniformizer order bound in the given geometric local
ring is at most the actual finite function-field extension degree. -/
theorem dominating_dvr_uniformizer_order_le_field_degree
    (π : A) (hπ : Irreducible π) (a : ℕ)
    (horder : algebraMap A B π ∈ (IsLocalRing.maximalIdeal B) ^ a) :
    a ≤ Module.finrank K L := by
  obtain ⟨q, hlie, e, he⟩ := dominating_dvr_normalization_prime_model (A := A) (B := B) (K := K) (L := L)
  let : q.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) := hlie
  have hmodel : algebraMap A (Localization.AtPrime q.asIdeal) π ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) ^ a := by
    apply (local_equiv_maximalIdeal_pow_mem_iff
      (A := Localization.AtPrime q.asIdeal) (B := B) e _ a).mp
    rw [he]
    exact horder
  exact dvr_normalization_uniformizer_order_le_field_degree (A := A) (K := K) (L := L)
    q.asIdeal π hπ a hmodel

end DimensionFourDependence
