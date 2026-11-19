import DimensionFourDependence.NormalizationCanonicalOrders

/-! # Canonical rational source-order comparison

This statement retains the actual local-ring map, a rational pullback
extending it, and every normalized discrete-valuation equality.
-/

namespace DimensionFourDependence

/-- A specified local map has a rational extension preserving every
normalized source valuation, and its target is itself a DVR. -/
noncomputable def CanonicalRationalSourceOrderComparison
    {O A F : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [IsDomain A] [Field F] [Algebra O F] [IsFractionRing O F]
    (f : O →+* A) : Prop :=
  ∃ hdvr : IsDiscreteValuationRing A,
    letI := hdvr
    letI : Algebra A (FractionRing A) := OreLocalization.instAlgebra
    ∃ j : F →+* FractionRing A,
      (∀ x : O, j (algebraMap O F x) = algebraMap A (FractionRing A) (f x)) ∧
      let v : IsDedekindDomain.HeightOneSpectrum O :=
        ⟨IsLocalRing.maximalIdeal O, inferInstance, IsDiscreteValuationRing.not_a_field O⟩
      let w : IsDedekindDomain.HeightOneSpectrum A :=
        ⟨IsLocalRing.maximalIdeal A, inferInstance, IsDiscreteValuationRing.not_a_field A⟩
      ∀ x : F, v.valuation F x = w.valuation (FractionRing A) (j x)

end DimensionFourDependence
