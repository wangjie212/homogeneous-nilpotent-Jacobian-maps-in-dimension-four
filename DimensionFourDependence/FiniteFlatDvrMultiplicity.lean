import DimensionFourDependence.FiniteFlatRamificationBound
import DimensionFourDependence.DvrOrderQuotientLength

/-! # Local uniformizer multiplicity is bounded by a finite projection's rank -/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {A S : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing S] [IsDedekindDomain S] [Algebra A S]
  [Module.Finite A S] [Module.Flat A S] [FaithfulSMul A S]

/-- The normalized local ring over the source DVR has a nonzero
pullback of every nonzero source function. -/
theorem finite_dedekind_prime_source_injective
    (q : Ideal S) [q.IsPrime] :
    Function.Injective (algebraMap A (Localization.AtPrime q)) := by
  rw [IsScalarTower.algebraMap_eq A S (Localization.AtPrime q)]
  exact (IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors).comp
    (FaithfulSMul.algebraMap_injective A S)

/-- The actual local vanishing order of a source uniformizer at every
prime of a finite flat normal cover is at most the projection rank. -/
theorem finite_flat_dedekind_uniformizer_order_le_rank
    (q : Ideal S) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal A)]
    (π : A) (hπ : Irreducible π) (a : ℕ)
    (horder : algebraMap A (Localization.AtPrime q) π ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a) :
    a ≤ Module.finrank A S := by
  have hq : q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field A) q
  let : IsDiscreteValuationRing (Localization.AtPrime q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq _
  have hπq : algebraMap A (Localization.AtPrime q) π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply finite_dedekind_prime_source_injective (A := A) q
    simpa only [map_zero] using h
  have hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A (Localization.AtPrime q)) =
      Ideal.span {algebraMap A (Localization.AtPrime q) π} := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hlength : (Module.length (Localization.AtPrime q)
      ((Localization.AtPrime q) ⧸ Ideal.span {algebraMap A (Localization.AtPrime q) π})).toNat =
        q.ramificationIdx A := by
    rw [Ideal.ramificationIdx_eq (IsLocalRing.maximalIdeal A) q, hmap]
  have hbound := dvr_power_order_le_quotient_length_toNat
    (algebraMap A (Localization.AtPrime q) π) hπq a horder
  rw [hlength] at hbound
  exact hbound.trans (finite_flat_ramification_index_le_rank (IsLocalRing.maximalIdeal A) q)

end DimensionFourDependence
