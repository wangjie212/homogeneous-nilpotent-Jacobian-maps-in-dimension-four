import DimensionFourDependence.RationalStalkPullbackComparison
import DimensionFourDependence.RationalSectionLocalOrder

/-! # Actual source-stalk pullbacks in every regular local frame -/

namespace DimensionFourDependence

/-- The rational geometric comparison, including invariance under
every regular frame transition unit in the actual source stalk. -/
noncomputable def FramedRationalStalkPullbackComparison
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
      (∀ x : F, v.valuation F x = w.valuation (FractionRing A) (j x)) ∧
        ∀ (u : Sˣ) (x : F),
          w.valuation (FractionRing A) (j (algebraMap O F (e (u : S)) * x)) = v.valuation F x

/-- The rational stalk comparison gives the same order in every
compatible regular local frame of a rational source section. -/
theorem rational_stalk_pullback_comparison_all_frames
    {S O A F : Type*} [CommRing S] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [IsDomain A] [Field F] [Algebra O F] [IsFractionRing O F]
    (e : S ≃+* O) (g : S →+* A) (h : RationalStalkPullbackComparison (F := F) e g) :
    FramedRationalStalkPullbackComparison (F := F) e g := by
  obtain ⟨hdvr, j, hj, hv⟩ := h
  let : IsDiscreteValuationRing A := hdvr
  let : Algebra A (FractionRing A) := OreLocalization.instAlgebra
  refine ⟨hdvr, j, hj, ?_⟩
  intro v w
  refine ⟨hv, ?_⟩
  intro u x
  exact rational_section_pullback_order_change_frame v (w.valuation (FractionRing A)) j hv
    (u.map e.toMonoidHom) x

end DimensionFourDependence
