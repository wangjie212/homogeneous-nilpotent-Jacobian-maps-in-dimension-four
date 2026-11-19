import DimensionFourDependence.ValuationLocalDescent

/-! # Rigidity of dominating birational extensions of valuation rings

A local overring of a source valuation ring in its same fraction field
equals the original source ring if it dominates that ring. This gives an
explicit local algebra isomorphism, with the original source map.
-/

namespace DimensionFourDependence

variable {A B F : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
  [CommRing B] [Field F] [Algebra A B] [Algebra A F] [Algebra B F]
  [IsScalarTower A B F] [IsFractionRing A F] [FaithfulSMul B F]
  [IsLocalHom (algebraMap A B)]

include F in
/-- The original local map of a dominating birational overring of a
valuation ring is bijective. -/
theorem valuation_local_overring_algebraMap_bijective :
    Function.Bijective (algebraMap A B) := by
  constructor
  · intro a a' haa'
    apply IsFractionRing.injective A F
    simpa only [← IsScalarTower.algebraMap_apply A B F] using congrArg (algebraMap B F) haa'
  · intro b
    obtain ⟨a, ha⟩ := valuation_source_fraction_regular_of_local_extension
      (A := A) (B := B) (F := F) (L := F) (algebraMap B F b) b (by rfl)
    refine ⟨a, ?_⟩
    apply FaithfulSMul.algebraMap_injective B F
    rw [← IsScalarTower.algebraMap_apply A B F]
    exact ha

/-- A dominating birational local overring is the original source
valuation ring, through its actual source algebra map. -/
noncomputable def valuationLocalOverringEquiv : A ≃ₐ[A] B :=
  AlgEquiv.ofBijective (Algebra.ofId A B) (valuation_local_overring_algebraMap_bijective (F := F))

end DimensionFourDependence
