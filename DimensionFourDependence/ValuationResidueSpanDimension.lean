import DimensionFourDependence.ValuationResidueLinearIndependence

/-! # Specializing integral coordinate values cannot increase their span dimension -/

namespace DimensionFourDependence

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K F A κ : Type*} [Field K] [Field F] [CommRing A] [Field κ]
  [Algebra K F]

/-- The span of a finite residue tuple over the coefficient residue
field has dimension at most that of its generic tuple over the coefficient
fraction field. No freeness or flat-family hypothesis is supplied. -/
theorem valuation_residue_span_finrank_le_generic
    (V : ValuationSubring K) [Algebra V A] [Algebra A F] [Algebra V F]
    [IsScalarTower V A F] [IsScalarTower V K F]
    [Algebra (IsLocalRing.ResidueField V) κ]
    (hinj : Function.Injective (algebraMap A F)) (π : A →+* κ)
    (hcompat : ∀ a : V, π (algebraMap V A a) =
      algebraMap (IsLocalRing.ResidueField V) κ (IsLocalRing.residue V a))
    {n : ℕ} (z : Fin n → A) :
    Module.finrank (IsLocalRing.ResidueField V)
        (Submodule.span (IsLocalRing.ResidueField V) (Set.range (fun i => π (z i)))) ≤
      Module.finrank K (Submodule.span K (Set.range (fun i => algebraMap A F (z i)))) := by
  classical
  obtain ⟨ι, f, hf, hspan, hLI⟩ := exists_linearIndependent' (IsLocalRing.ResidueField V) (fun i => π (z i))
  let : Finite ι := Finite.of_injective f hf
  let : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  have hresLI : LinearIndependent (IsLocalRing.ResidueField V)
      (fun j : Fin (Fintype.card ι) => π (z (f (e.symm j)))) :=
    hLI.comp e.symm e.symm.injective
  have hgenericLI := valuation_residue_linearIndependent_lifts V hinj π hcompat
    (fun j : Fin (Fintype.card ι) => z (f (e.symm j))) hresLI
  have hresDim := finrank_span_eq_card hLI
  rw [hspan] at hresDim
  have hgenericDim := finrank_span_eq_card hgenericLI
  simp only [Fintype.card_fin] at hgenericDim
  let : Module.Finite K (Submodule.span K (Set.range (fun i => algebraMap A F (z i)))) :=
    Module.Finite.span_of_finite K (Set.finite_range _)
  have hle : Submodule.span K
      (Set.range (fun j : Fin (Fintype.card ι) => algebraMap A F (z (f (e.symm j))))) ≤
      Submodule.span K (Set.range (fun i => algebraMap A F (z i))) := by
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨f (e.symm j), rfl⟩
  rw [hresDim, ← hgenericDim]
  exact Submodule.finrank_mono hle

end DimensionFourDependence
