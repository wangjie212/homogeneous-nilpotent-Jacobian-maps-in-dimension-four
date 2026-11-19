import DimensionFourDependence.CanonicalRationalOrderComparison

/-! # Rational pullbacks determined by the actual source stalk

The source coordinate localization is identified with the entire actual
source stalk. A rational comparison extending its local map therefore
extends the actual geometric stalk map and is uniquely determined by it.
-/

namespace DimensionFourDependence

/-- A rational pullback extends every actual source-stalk value and
preserves the normalized source-divisor valuation. -/
noncomputable def RationalStalkPullbackComparison
    {S O A F : Type*} [CommRing S] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [IsDomain A] [Field F] [Algebra O F] [IsFractionRing O F]
    (e : S ≃+* O) (g : S →+* A) : Prop :=
  ∃ hdvr : IsDiscreteValuationRing A,
    letI := hdvr
    letI : Algebra A (FractionRing A) := OreLocalization.instAlgebra
    ∃ j : F →+* FractionRing A,
      (∀ z : S, j (algebraMap O F (e z)) = algebraMap A (FractionRing A) (g z)) ∧
      let v : IsDedekindDomain.HeightOneSpectrum O :=
        ⟨IsLocalRing.maximalIdeal O, inferInstance, IsDiscreteValuationRing.not_a_field O⟩
      let w : IsDedekindDomain.HeightOneSpectrum A :=
        ⟨IsLocalRing.maximalIdeal A, inferInstance, IsDiscreteValuationRing.not_a_field A⟩
      ∀ x : F, v.valuation F x = w.valuation (FractionRing A) (j x)

/-- A canonical rational comparison compatible with the entire source
stalk is the rational comparison for that actual stalk pullback. -/
theorem canonical_rational_comparison_to_stalk_pullback
    {S O A F : Type*} [CommRing S] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [IsDomain A] [Field F] [Algebra O F] [IsFractionRing O F]
    (e : S ≃+* O) (f : O →+* A) (g : S →+* A) (hfg : ∀ z, f (e z) = g z)
    (h : CanonicalRationalSourceOrderComparison (F := F) f) :
    RationalStalkPullbackComparison (F := F) e g := by
  obtain ⟨hdvr, j, hj, hv⟩ := h
  let : IsDiscreteValuationRing A := hdvr
  let : Algebra A (FractionRing A) := OreLocalization.instAlgebra
  refine ⟨hdvr, j, ?_, hv⟩
  intro z
  exact (hj (e z)).trans (congrArg (algebraMap A (FractionRing A)) (hfg z))

/-- The rational extension is uniquely fixed by its values on the
entire actual source stalk, independent of any chosen local model. -/
theorem rational_source_stalk_pullback_unique
    {S O A F : Type*} [CommRing S] [CommRing O] [IsDomain O]
    [CommRing A] [IsDomain A] [Field F] [Algebra O F] [IsFractionRing O F]
    (e : S ≃+* O) (g : S →+* A) (j k : F →+* FractionRing A)
    (hj : ∀ z : S, j (algebraMap O F (e z)) = algebraMap A (FractionRing A) (g z))
    (hk : ∀ z : S, k (algebraMap O F (e z)) = algebraMap A (FractionRing A) (g z)) : j = k := by
  apply IsFractionRing.ringHom_ext (A := O)
  intro x
  simpa only [RingEquiv.apply_symm_apply] using (hj (e.symm x)).trans (hk (e.symm x)).symm

end DimensionFourDependence
