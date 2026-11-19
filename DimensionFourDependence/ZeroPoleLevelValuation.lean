import DimensionFourDependence.ZeroPoleLocalReciprocal

/-! # A dominating valuation specializing to a translated level

For an integrally closed local subring, the zero/pole obstruction to
regularity constructs a valuation dominating the closed point in which
the function has the prescribed residue. This is a valuative statement;
it does not assert closure of the level on the original source scheme.
-/

namespace DimensionFourDependence

variable {F : Type*} [Field F]

/-- A missing level reciprocal in a normal local subring constructs
a valuation dominating that local ring in which the level difference
is in the maximal ideal. -/
theorem nonregular_level_reciprocal_constructs_dominating_valuation
    (R : LocalSubring F) [IsIntegrallyClosedIn R.toSubring F]
    (f c : F) (hc : c ∈ R.toSubring)
    (hreg : (f - c)⁻¹ ∉ R.toSubring) :
    ∃ V : ValuationSubring F, R ≤ V.toLocalSubring ∧
      f ∈ V ∧ f - c ∈ V.nonunits := by
  obtain ⟨V, hdom, hnot⟩ :=
    LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn hreg
  have hdiff : f - c ∈ V.nonunits := by
    have hi : ((f - c)⁻¹)⁻¹ ∈ V.nonunits :=
      V.inv_mem_nonunits_iff.mpr (Or.inr hnot)
    simpa only [inv_inv] using hi
  refine ⟨V, hdom, ?_, hdiff⟩
  have hsum := V.toSubring.add_mem (V.nonunits_subset hdiff) (hdom.1 hc)
  rw [sub_add_cancel] at hsum
  exact hsum

/-- If the zero and pole branch centers lie below the closed point
of a normal local ring, every distinct level has an actual valuation
centered at that point with the prescribed residue. -/
theorem zero_pole_constructs_dominating_level_valuation
    (R : LocalSubring F) [IsIntegrallyClosedIn R.toSubring F]
    (f c : F) (hc : c ∈ R.toSubring)
    (V₀ Vinf : ValuationSubring F)
    (hR₀ : R.toSubring ≤ V₀.toSubring) (hRinf : R.toSubring ≤ Vinf.toSubring)
    (hzero : f ∈ V₀.nonunits) (hpole : f⁻¹ ∈ Vinf.nonunits)
    (hf : f ≠ 0) (hlevel : f ≠ c) :
    ∃ V : ValuationSubring F, R ≤ V.toLocalSubring ∧
      f ∈ V ∧ f - c ∈ V.nonunits :=
  nonregular_level_reciprocal_constructs_dominating_valuation R f c hc
    (zero_pole_level_reciprocal_not_mem_local_subring
      R f c hc V₀ Vinf hR₀ hRinf hzero hpole hf hlevel)

/-- The constructed valuation realizes equality of the actual
residues of the function and the level constant. -/
theorem zero_pole_constructs_dominating_level_residue
    (R : LocalSubring F) [IsIntegrallyClosedIn R.toSubring F]
    (f c : F) (hc : c ∈ R.toSubring)
    (V₀ Vinf : ValuationSubring F)
    (hR₀ : R.toSubring ≤ V₀.toSubring) (hRinf : R.toSubring ≤ Vinf.toSubring)
    (hzero : f ∈ V₀.nonunits) (hpole : f⁻¹ ∈ Vinf.nonunits)
    (hf : f ≠ 0) (hlevel : f ≠ c) :
    ∃ (V : ValuationSubring F) (hdom : R ≤ V.toLocalSubring) (hfV : f ∈ V),
      IsLocalRing.residue V ⟨f, hfV⟩ =
        IsLocalRing.residue V ⟨c, hdom.1 hc⟩ := by
  obtain ⟨V, hdom, hfV, hd⟩ := zero_pole_constructs_dominating_level_valuation
    R f c hc V₀ Vinf hR₀ hRinf hzero hpole hf hlevel
  refine ⟨V, hdom, hfV, ?_⟩
  apply sub_eq_zero.mp
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact V.coe_mem_nonunits_iff.mp hd

end DimensionFourDependence
