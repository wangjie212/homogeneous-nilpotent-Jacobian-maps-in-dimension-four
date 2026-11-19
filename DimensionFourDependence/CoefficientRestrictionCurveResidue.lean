import DimensionFourDependence.CoefficientRestrictionHilbertComparison
import DimensionFourDependence.CurveValuationResidueAlgebraic

/-! # A regular pencil zero constructs an algebraic coefficient residue field -/

namespace DimensionFourDependence

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {A F : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  (C : Type*) [Field C] [Algebra C F]

/-- An actual nonzero regular coefficient zero restricts to a
nonzero element with zero residue in the constructed coefficient valuation. -/
theorem coefficientRestriction_regular_zero
    (c : C) (f : A) (hf : f ≠ 0) (hzero : f ∈ IsLocalRing.maximalIdeal A)
    (hvalue : algebraMap A F f = algebraMap C F c) :
    ∃ t : coefficientRestrictionValuationSubring (A := A) (F := F) C,
      (t : C) = c ∧ t ≠ 0 ∧ IsLocalRing.residue _ t = 0 := by
  let V := coefficientRestrictionValuationSubring (A := A) (F := F) C
  let t : V := ⟨c, (coefficientRestrictionValuationSubring_mem_iff
    (A := A) (F := F) C c).mpr ⟨f, hvalue⟩⟩
  have ht : coefficientRestrictionLocalHom (A := A) (F := F) C t = f := by
    apply IsFractionRing.injective A F
    rw [coefficientRestrictionLocalHom_source]
    exact hvalue.symm
  refine ⟨t, rfl, ?_, ?_⟩
  · intro hz
    apply hf
    rw [← ht, hz, map_zero]
  · apply (coefficientRestrictionResidueHom (A := A) (F := F) C).injective
    rw [map_zero, coefficientRestrictionResidueHom_residue, ht]
    exact (IsLocalRing.residue_eq_zero_iff f).mpr hzero

variable (E : Type*) [Field E] [Algebra E A] [Algebra E C] [Algebra E F]
  [IsScalarTower E A F] [IsScalarTower E C F]

/-- Original constants lie in the restricted coefficient valuation
because their specified source values are regular constant germs. -/
theorem coefficientRestriction_constants_mem (c : E) :
    algebraMap E C c ∈ coefficientRestrictionValuationSubring (A := A) (F := F) C := by
  apply (coefficientRestrictionValuationSubring_mem_iff (A := A) (F := F) C _).mpr
  exact ⟨algebraMap E A c, (IsScalarTower.algebraMap_apply E A F c).symm.trans
    (IsScalarTower.algebraMap_apply E C F c)⟩

/-- The restricted valuation inherits the original constant-field action. -/
@[instance_reducible]
noncomputable def coefficientRestrictionConstantAlgebra :
    Algebra E (coefficientRestrictionValuationSubring (A := A) (F := F) C) :=
  valuationConstantAlgebra _ (coefficientRestriction_constants_mem (A := A) (F := F) C E)

/-- Its action on the coefficient field is the original one. -/
theorem coefficientRestrictionConstantAlgebra_scalarTower :
    letI := coefficientRestrictionConstantAlgebra (A := A) (F := F) C E
    IsScalarTower E (coefficientRestrictionValuationSubring (A := A) (F := F) C) C :=
  valuationConstantScalarTower _ (coefficientRestriction_constants_mem (A := A) (F := F) C E)

/-- The actual regular coefficient zero makes the coefficient
valuation nontrivial. Curve dimension then constructs algebraicity of
its entire residue field over the original constants. -/
theorem source_valuation_coefficient_restriction_curve_residue_isAlgebraic
    (c : C) (f : A) (hf : f ≠ 0) (hzero : f ∈ IsLocalRing.maximalIdeal A)
    (hvalue : algebraMap A F f = algebraMap C F c)
    (htr : Algebra.trdeg E C ≤ 1) :
    letI := coefficientRestrictionConstantAlgebra (A := A) (F := F) C E
    Algebra.IsAlgebraic E (IsLocalRing.ResidueField
      (coefficientRestrictionValuationSubring (A := A) (F := F) C)) := by
  let V := coefficientRestrictionValuationSubring (A := A) (F := F) C
  letI := coefficientRestrictionConstantAlgebra (A := A) (F := F) C E
  letI := coefficientRestrictionConstantAlgebra_scalarTower (A := A) (F := F) C E
  obtain ⟨t, htc, ht, hres⟩ := coefficientRestriction_regular_zero
    (A := A) (F := F) C c f hf hzero hvalue
  have hc : c ≠ 0 := by
    intro hz
    apply ht
    apply Subtype.ext
    exact htc.trans hz
  have hv : V.valuation c < 1 := by
    have he := (valuation_residue_zero_iff V t).mp hres
    rwa [htc] at he
  have hpole : 1 < V.valuation c⁻¹ := by
    rw [map_inv₀]
    exact (one_lt_inv₀ (pos_iff_ne_zero.mpr ((map_ne_zero V.valuation).mpr hc))).mpr hv
  exact curve_valuation_residue_isAlgebraic V c⁻¹ hpole htr

end DimensionFourDependence
