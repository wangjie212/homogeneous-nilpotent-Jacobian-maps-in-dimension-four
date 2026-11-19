import DimensionFourDependence.CanonicalRationalOrderComparison
import DimensionFourDependence.LocalEquivRationalOrder

/-! # Canonical rational orders survive actual local-ring identification

A local-ring isomorphism transports the full rational comparison, not
only maximal-ideal power membership. Compatible comparisons compose.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

/-- An actual local-ring identification preserves every normalized
valuation and extends its specified inverse on regular functions. -/
theorem local_equiv_canonical_rational_order_comparison
    {A B F : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field F] [Algebra B F] [IsFractionRing B F] (e : A ≃+* B) :
    CanonicalRationalSourceOrderComparison (F := F) e.symm.toRingHom := by
  let : Algebra B A := e.symm.toRingHom.toAlgebra
  let eA : A ≃ₐ[B] B :=
    { e with
      commutes' := by
        intro r
        change e (e.symm r) = r
        exact e.apply_symm_apply r }
  let hdvr : IsDiscreteValuationRing A := local_equiv_isDiscreteValuationRing e
  let : IsDiscreteValuationRing A := hdvr
  let j : F →+* FractionRing A := (localEquivSourceFractionHom (O := B) (F := F) eA).toRingHom
  refine ⟨hdvr, j, ?_, ?_⟩
  · intro x
    change localEquivSourceFractionHom (O := B) (F := F) eA (algebraMap B F x) =
      algebraMap A (FractionRing A) (e.symm x)
    have h := localEquivSourceFractionHom_algebraMap (O := B) (F := F) eA x
    have hx : localEquivSourceAlgHom (O := B) eA x = e.symm x := by rfl
    simpa only [hx] using h
  · exact localEquivSource_rational_order (O := B) (F := F) eA

/-- Composing source-compatible rational comparisons preserves the
entire canonical rational comparison and its normalized valuations. -/
theorem canonical_rational_source_order_comparison_comp
    {O A B F : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field F] [Algebra O F] [IsFractionRing O F]
    (f : O →+* A) (g : A →+* B)
    (hf : CanonicalRationalSourceOrderComparison (F := F) f)
    (hg : ∀ hdvr : IsDiscreteValuationRing A,
      letI := hdvr
      letI : Algebra A (FractionRing A) := OreLocalization.instAlgebra
      CanonicalRationalSourceOrderComparison (F := FractionRing A) g) :
    CanonicalRationalSourceOrderComparison (F := F) (g.comp f) := by
  obtain ⟨hdvrA, j, hj, hv⟩ := hf
  let : IsDiscreteValuationRing A := hdvrA
  let : Algebra A (FractionRing A) := OreLocalization.instAlgebra
  obtain ⟨hdvrB, k, hk, hw⟩ := hg hdvrA
  let : IsDiscreteValuationRing B := hdvrB
  let : Algebra B (FractionRing B) := OreLocalization.instAlgebra
  refine ⟨hdvrB, k.comp j, ?_, ?_⟩
  · intro x
    change k (j (algebraMap O F x)) = algebraMap B (FractionRing B) (g (f x))
    rw [hj, hk]
  · intro v w x
    exact (hv x).trans (hw (j x))

end DimensionFourDependence
