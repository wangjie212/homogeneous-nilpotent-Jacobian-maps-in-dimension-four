import DimensionFourDependence.RationalComparisonFractionField
import DimensionFourDependence.FramedRationalStalkComparison

/-! # Intrinsic divisor orders for an actual local-ring pullback

This formulation uses the source stalk and its own fraction field.
No coordinate prime, auxiliary local model, or independently chosen
rational pullback appears among its parameters.
-/

namespace DimensionFourDependence

/-- The actual source and target are DVRs; the actual source-local
map extends to rational functions with every normalized valuation and
regular local-frame order preserved, and all regular order bounds agree. -/
noncomputable def IntrinsicDivisorPullbackComparison
    {S A : Type*} [CommRing S] [IsLocalRing S] [CommRing A] [IsLocalRing A]
    (g : S →+* A) : Prop :=
  ∃ hS : IsDomain S, ∃ hA : IsDomain A,
    letI := hS
    letI := hA
    ∃ hDVR : IsDiscreteValuationRing S,
      letI := hDVR
      FramedRationalStalkPullbackComparison (F := FractionRing S) (RingEquiv.refl S) g ∧
        ∀ (z : S) (n : ℕ),
          g z ∈ (IsLocalRing.maximalIdeal A) ^ n ↔ z ∈ (IsLocalRing.maximalIdeal S) ^ n

/-- A source-compatible rational comparison in any checked source
coordinates gives the intrinsic statement for the entire actual map. -/
theorem intrinsic_divisor_pullback_of_source_comparison
    {S O A F : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field F] [Algebra O F] [IsFractionRing O F]
    (e : S ≃+* O) (g : S →+* A)
    (h : RationalStalkPullbackComparison (F := F) e g)
    (hregular : ∀ (z : S) (n : ℕ),
      g z ∈ (IsLocalRing.maximalIdeal A) ^ n ↔ z ∈ (IsLocalRing.maximalIdeal S) ^ n) :
    IntrinsicDivisorPullbackComparison g := by
  have hcanonical := rational_stalk_comparison_intrinsic_source e g h
  have hraw := canonical_rational_comparison_to_stalk_pullback
    (RingEquiv.refl S) g g (fun _ => rfl) hcanonical
  have hframed := rational_stalk_pullback_comparison_all_frames (RingEquiv.refl S) g hraw
  exact ⟨inferInstance, inferInstance, inferInstance, hframed, hregular⟩

end DimensionFourDependence
