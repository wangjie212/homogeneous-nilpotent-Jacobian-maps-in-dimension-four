import DimensionFourDependence.IntrinsicDivisorPullback

/-! # Intrinsic divisor comparisons survive local-ring isomorphisms

Both local rings may be identified with other actual stalks. The
comparison transports regular orders, the rational pullback, and all
regular frame transitions through the commuting square.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

/-- A commuting square of local-ring isomorphisms transports the entire
intrinsic divisor comparison, including its actual regular pullback. -/
theorem intrinsic_divisor_pullback_equiv
    {S T A B : Type*} [CommRing S] [IsLocalRing S]
    [CommRing T] [IsLocalRing T] [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B]
    (s : S ≃+* T) (a : A ≃+* B) (f : S →+* A) (g : T →+* B)
    (h : ∀ z : S, a (f z) = g (s z))
    (hf : IntrinsicDivisorPullbackComparison f) :
    IntrinsicDivisorPullbackComparison g := by
  obtain ⟨hS, hA, hDVR, hframed, hregular⟩ := hf
  let : IsDomain S := hS
  let : IsDomain A := hA
  let : IsDiscreteValuationRing S := hDVR
  let : IsDomain T := Function.Injective.isDomain s.symm s.symm.injective
  let : IsDomain B := Function.Injective.isDomain a.symm a.symm.injective
  let : IsDiscreteValuationRing T := local_equiv_isDiscreteValuationRing s.symm
  let : Algebra S (FractionRing S) := OreLocalization.instAlgebra
  obtain ⟨hDVRA, j, hj, hv, _hframes⟩ := hframed
  let : IsDiscreteValuationRing A := hDVRA
  let : Algebra A (FractionRing A) := OreLocalization.instAlgebra
  have hcanonical : CanonicalRationalSourceOrderComparison (F := FractionRing S) f :=
    ⟨hDVRA, j, hj, hv⟩
  have htarget : CanonicalRationalSourceOrderComparison (F := FractionRing A) a.toRingHom :=
    local_equiv_canonical_rational_order_comparison (A := B) (B := A) a.symm
  have hcomp := canonical_rational_source_order_comparison_comp f a.toRingHom
    hcanonical (fun _ => htarget)
  have hcompat : ∀ z : T, (a.toRingHom.comp f) (s.symm z) = g z := by
    intro z
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] using h (s.symm z)
  have hrational := canonical_rational_comparison_to_stalk_pullback
    (F := FractionRing S) s.symm (a.toRingHom.comp f) g hcompat hcomp
  apply intrinsic_divisor_pullback_of_source_comparison s.symm g hrational
  intro z n
  rw [← hcompat z]
  exact (local_equiv_maximalIdeal_pow_mem_iff a (f (s.symm z)) n).trans
    ((hregular (s.symm z) n).trans
      (local_equiv_maximalIdeal_pow_mem_iff s.symm z n))

end DimensionFourDependence
