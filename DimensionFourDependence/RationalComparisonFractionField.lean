import DimensionFourDependence.LocalEquivCanonicalRationalOrders
import DimensionFourDependence.RationalStalkPullbackComparison

/-! # Rational comparisons are independent of fraction-field coordinates -/

namespace DimensionFourDependence

variable {O F G : Type*} [CommRing O] [IsDedekindDomain O]
  [Field F] [Algebra O F] [IsFractionRing O F]
  [Field G] [Algebra O G] [IsFractionRing O G]

/-- A fraction-field identification preserving the original ring
preserves every normalized divisor valuation. -/
theorem divisor_valuation_fraction_field_map
    (v : IsDedekindDomain.HeightOneSpectrum O) (j : F →+* G)
    (hj : ∀ r : O, j (algebraMap O F r) = algebraMap O G r) (x : F) :
    v.valuation F x = v.valuation G (j x) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective O x
  rw [map_div₀, map_div₀, hj, hj, map_div₀]
  simp only [v.valuation_of_algebraMap]

/-- The rational comparison can be restated in any fraction field
of the same source ring. -/
theorem canonical_rational_comparison_change_fraction_field
    {O A F G : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [IsDomain A]
    [Field F] [Algebra O F] [IsFractionRing O F]
    [Field G] [Algebra O G] [IsFractionRing O G]
    (f : O →+* A) (h : CanonicalRationalSourceOrderComparison (F := F) f) :
    CanonicalRationalSourceOrderComparison (F := G) f := by
  obtain ⟨hdvr, j, hj, hv⟩ := h
  let : IsDiscreteValuationRing A := hdvr
  let : Algebra A (FractionRing A) := OreLocalization.instAlgebra
  let k : G ≃ₐ[O] F := IsLocalization.algEquiv (nonZeroDivisors O) G F
  refine ⟨hdvr, j.comp k.toRingHom, ?_, ?_⟩
  · intro r
    change j (k (algebraMap O G r)) = _
    rw [k.commutes, hj]
  · intro v w x
    exact (divisor_valuation_fraction_field_map v k.toRingHom k.commutes x).trans (hv (k x))

/-- A comparison expressed in an identified source localization is
intrinsically the comparison for the fraction field of the source stalk. -/
theorem rational_stalk_comparison_intrinsic_source
    {S O A F : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [IsDomain A] [Field F] [Algebra O F] [IsFractionRing O F]
    (e : S ≃+* O) (g : S →+* A)
    (h : RationalStalkPullbackComparison (F := F) e g) :
    CanonicalRationalSourceOrderComparison (F := FractionRing S) g := by
  have hO : CanonicalRationalSourceOrderComparison (F := F) (g.comp e.symm.toRingHom) := by
    obtain ⟨hdvr, j, hj, hv⟩ := h
    refine ⟨hdvr, j, ?_, hv⟩
    intro r
    change j (algebraMap O F r) = algebraMap A (FractionRing A) (g (e.symm r))
    simpa only [RingEquiv.apply_symm_apply] using hj (e.symm r)
  have hOf : CanonicalRationalSourceOrderComparison (F := FractionRing O)
      (g.comp e.symm.toRingHom) := canonical_rational_comparison_change_fraction_field _ hO
  have he : CanonicalRationalSourceOrderComparison (F := FractionRing S) e.toRingHom :=
    local_equiv_canonical_rational_order_comparison (A := O) (B := S) e.symm
  have hcomp := canonical_rational_source_order_comparison_comp e.toRingHom
    (g.comp e.symm.toRingHom) he (fun _ => hOf)
  have hmap : (g.comp e.symm.toRingHom).comp e.toRingHom = g := by
    ext r
    change g (e.symm (e r)) = g r
    rw [e.symm_apply_apply]
  rw [hmap] at hcomp
  exact hcomp

end DimensionFourDependence
