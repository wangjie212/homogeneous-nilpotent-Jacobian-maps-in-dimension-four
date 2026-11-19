import DimensionFourDependence.CoefficientRestrictionValuation

/-! # The actual source valuation constructs its coefficient-compatible Hilbert comparison -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {A F : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  (C : Type*) [Field C] [Algebra C F]

/-- The coefficient valuation acts on the actual source ring through
its constructed local embedding. -/
@[instance_reducible]
noncomputable def coefficientRestrictionLocalAlgebra :
    Algebra (coefficientRestrictionValuationSubring (A := A) (F := F) C) A :=
  (coefficientRestrictionLocalHom (A := A) (F := F) C).toAlgebra

/-- Its fraction-field action retains the original coefficient-field embedding. -/
@[instance_reducible]
noncomputable def coefficientRestrictionFractionAlgebra :
    Algebra (coefficientRestrictionValuationSubring (A := A) (F := F) C) F :=
  ((algebraMap C F).comp (coefficientRestrictionValuationSubring (A := A) (F := F) C).subtype).toAlgebra

/-- The coefficient and source residue fields have their constructed
compatible scalar action. -/
@[instance_reducible]
noncomputable def coefficientRestrictionResidueAlgebra :
    Algebra (IsLocalRing.ResidueField (coefficientRestrictionValuationSubring (A := A) (F := F) C))
      (IsLocalRing.ResidueField A) :=
  (coefficientRestrictionResidueHom (A := A) (F := F) C).toAlgebra

/-- Both paths to the source fraction field use exactly the same
regular coefficient representative. -/
theorem coefficientRestrictionLocalAlgebra_scalarTower :
    letI := coefficientRestrictionLocalAlgebra (A := A) (F := F) C
    letI := coefficientRestrictionFractionAlgebra (A := A) (F := F) C
    IsScalarTower (coefficientRestrictionValuationSubring (A := A) (F := F) C) A F := by
  letI := coefficientRestrictionLocalAlgebra (A := A) (F := F) C
  letI := coefficientRestrictionFractionAlgebra (A := A) (F := F) C
  exact IsScalarTower.of_algebraMap_eq (fun c =>
    (coefficientRestrictionLocalHom_source (A := A) (F := F) C c).symm)

/-- Restriction of the original coefficient field also preserves
the same fraction-field action. -/
theorem coefficientRestrictionFractionAlgebra_scalarTower :
    letI := coefficientRestrictionFractionAlgebra (A := A) (F := F) C
    IsScalarTower (coefficientRestrictionValuationSubring (A := A) (F := F) C) C F := by
  letI := coefficientRestrictionFractionAlgebra (A := A) (F := F) C
  exact IsScalarTower.of_algebraMap_eq' rfl

variable {σ : Type*} [Finite σ]

/-- The actual source valuation and specified coefficient field
construct their Hilbert-function comparison without supplied valuation,
residue embedding or scalar-compatibility hypotheses. -/
theorem source_valuation_coefficient_restriction_hilbert_bound
    (z : σ → A) (d : ℕ) :
    letI := coefficientRestrictionResidueAlgebra (A := A) (F := F) C
    projectiveHilbertFunction
        (projectiveFieldPointIdeal
          (E := IsLocalRing.ResidueField (coefficientRestrictionValuationSubring (A := A) (F := F) C))
          (fun i => IsLocalRing.residue A (z i))).toIdeal d ≤
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := C)
        (fun i => algebraMap A F (z i))).toIdeal d := by
  let V := coefficientRestrictionValuationSubring (A := A) (F := F) C
  let aVA := coefficientRestrictionLocalAlgebra (A := A) (F := F) C
  let aVF := coefficientRestrictionFractionAlgebra (A := A) (F := F) C
  let tVAF := coefficientRestrictionLocalAlgebra_scalarTower (A := A) (F := F) C
  let tVCF := coefficientRestrictionFractionAlgebra_scalarTower (A := A) (F := F) C
  let aResidue := coefficientRestrictionResidueAlgebra (A := A) (F := F) C
  apply projectiveHilbertFunction_residue_le_generic V (IsFractionRing.injective A F) (IsLocalRing.residue A)
  intro c
  exact (coefficientRestrictionResidueHom_residue (A := A) (F := F) C c).symm

/-- The actual source valuation constructs the normalized projective
curve-degree bound over the restricted coefficient residue field. -/
theorem source_valuation_coefficient_restriction_curve_degree_bound
    (x : σ → F) (s : F) (hs : s ≠ 0) (z : σ → A)
    (hz : ∀ i, algebraMap A F (z i) = s * x i)
    {e e' : ℕ} (he : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C) x).toIdeal e) :
    letI := coefficientRestrictionResidueAlgebra (A := A) (F := F) C
    HasCurveHilbertDegree
      (projectiveFieldPointIdeal
        (E := IsLocalRing.ResidueField (coefficientRestrictionValuationSubring (A := A) (F := F) C))
        (fun i => IsLocalRing.residue A (z i))).toIdeal e' → e' ≤ e := by
  let aResidue := coefficientRestrictionResidueAlgebra (A := A) (F := F) C
  intro he'
  apply curveHilbertDegree_le_of_hilbertFunction_le _ _ ?_ he he'
  intro d
  have hb := source_valuation_coefficient_restriction_hilbert_bound (A := A) (F := F) C z d
  have hcoords : (fun i => algebraMap A F (z i)) = (fun i => s * x i) := funext hz
  rwa [hcoords, projectiveFieldPointIdeal_scale x s hs] at hb

end DimensionFourDependence
