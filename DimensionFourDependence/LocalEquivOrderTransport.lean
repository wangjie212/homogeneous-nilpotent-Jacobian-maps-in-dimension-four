import DimensionFourDependence.Defs
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Local isomorphisms preserve divisor orders

The constructed normalization local isomorphism transports maximal-ideal
power membership exactly. This is the order invariant needed when using
the unramified source model for locally represented rational sections.
-/

namespace DimensionFourDependence

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]

/-- Every maximal-ideal power maps to the same power through a local
ring isomorphism. -/
theorem local_equiv_map_maximalIdeal_pow (e : A ≃+* B) (a : ℕ) :
    ((IsLocalRing.maximalIdeal A) ^ a).map e.toRingHom = (IsLocalRing.maximalIdeal B) ^ a := by
  rw [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective]

/-- Maximal-ideal order bounds are unchanged by the constructed local
normalization isomorphism. -/
theorem local_equiv_maximalIdeal_pow_mem_iff (e : A ≃+* B) (x : A) (a : ℕ) :
    e x ∈ (IsLocalRing.maximalIdeal B) ^ a ↔ x ∈ (IsLocalRing.maximalIdeal A) ^ a := by
  change x ∈ ((IsLocalRing.maximalIdeal B) ^ a).comap e.toRingHom ↔ _
  rw [← local_equiv_map_maximalIdeal_pow e a,
    Ideal.comap_map_of_bijective e.toRingHom e.bijective]

/-- Any compatible local representation of a source function has the
same maximal-ideal order after local-ring identification. -/
theorem local_equiv_source_order_iff {R : Type*} [CommRing R]
    (e : A ≃+* B) (f : R →+* A) (g : R →+* B)
    (h : ∀ r, e (f r) = g r) (r : R) (a : ℕ) :
    g r ∈ (IsLocalRing.maximalIdeal B) ^ a ↔ f r ∈ (IsLocalRing.maximalIdeal A) ^ a := by
  rw [← h r]
  exact local_equiv_maximalIdeal_pow_mem_iff e (f r) a

variable [IsDomain A] [IsDomain B] [IsDiscreteValuationRing B]

omit [IsLocalRing B] in
/-- A local ring identified with the unramified source DVR is itself a
DVR; this does not assume that property of the normalization local ring. -/
theorem local_equiv_isDiscreteValuationRing (e : A ≃+* B) : IsDiscreteValuationRing A := by
  let : IsPrincipalIdealRing A := IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
  refine { toIsPrincipalIdealRing := inferInstance, toIsLocalRing := inferInstance, not_a_field' := ?_ }
  intro h
  have hm := IsLocalRing.map_ringEquiv_maximalIdeal e
  rw [h, Ideal.map_bot] at hm
  exact IsDiscreteValuationRing.not_a_field B hm.symm

end DimensionFourDependence
