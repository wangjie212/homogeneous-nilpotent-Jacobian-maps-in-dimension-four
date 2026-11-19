import DimensionFourDependence.CoefficientRestrictionCurveResidue

/-! # Restricted coefficient residues retain a specified local field realization -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {A G : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
  [Field G] [Algebra A G] [IsFractionRing A G]
  (C : Type*) [Field C] [Algebra C G]

/-- A specified local realization of the source ring realizes its
restricted coefficient residue field in the same target field. -/
noncomputable def coefficientRestrictionResidueFieldHom
    {F : Type*} [Field F] (π : A →+* F) [IsLocalHom π] :
    IsLocalRing.ResidueField (coefficientRestrictionValuationSubring (A := A) (F := G) C) →+* F :=
  (IsLocalRing.ResidueField.lift π).comp
    (coefficientRestrictionResidueHom (A := A) (F := G) C)

/-- Every restricted coefficient keeps exactly the specified
local source value under the constructed residue realization. -/
theorem coefficientRestrictionResidueFieldHom_residue
    {F : Type*} [Field F] (π : A →+* F) [IsLocalHom π]
    (c : coefficientRestrictionValuationSubring (A := A) (F := G) C) :
    coefficientRestrictionResidueFieldHom (A := A) (G := G) C π (IsLocalRing.residue _ c) =
      π (coefficientRestrictionLocalHom (A := A) (F := G) C c) := rfl

/-- The projective Hilbert comparison lands directly in the specified
local field realization, without identifying an abstract source residue field. -/
theorem source_valuation_realized_coefficient_residue_hilbert_bound
    {F σ : Type*} [Field F] [Finite σ] (π : A →+* F) [IsLocalHom π]
    (z : σ → A) (n : ℕ) :
    letI := (coefficientRestrictionResidueFieldHom (A := A) (G := G) C π).toAlgebra
    projectiveHilbertFunction (projectiveFieldPointIdeal
      (E := IsLocalRing.ResidueField (coefficientRestrictionValuationSubring (A := A) (F := G) C))
      (fun i => π (z i))).toIdeal n ≤
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := C)
      (fun i => algebraMap A G (z i))).toIdeal n := by
  let V := coefficientRestrictionValuationSubring (A := A) (F := G) C
  let aVA := coefficientRestrictionLocalAlgebra (A := A) (F := G) C
  let aVG := coefficientRestrictionFractionAlgebra (A := A) (F := G) C
  let tVAG := coefficientRestrictionLocalAlgebra_scalarTower (A := A) (F := G) C
  let tVCG := coefficientRestrictionFractionAlgebra_scalarTower (A := A) (F := G) C
  letI := (coefficientRestrictionResidueFieldHom (A := A) (G := G) C π).toAlgebra
  apply projectiveHilbertFunction_residue_le_generic V (IsFractionRing.injective A G) π
  intro c
  exact (coefficientRestrictionResidueFieldHom_residue (A := A) (G := G) C π c).symm

variable (E : Type*) [Field E] [Algebra E A] [Algebra E C] [Algebra E G]
  [IsScalarTower E A G] [IsScalarTower E C G]

/-- Restriction preserves every original constant in the actual
local source ring, not only its value in the source fraction field. -/
theorem coefficientRestrictionLocalHom_constant (c : E) :
    letI := coefficientRestrictionConstantAlgebra (A := A) (F := G) C E
    coefficientRestrictionLocalHom (A := A) (F := G) C
      (algebraMap E (coefficientRestrictionValuationSubring (A := A) (F := G) C) c) =
      algebraMap E A c := by
  letI := coefficientRestrictionConstantAlgebra (A := A) (F := G) C E
  apply IsFractionRing.injective A G
  rw [coefficientRestrictionLocalHom_source, ← IsScalarTower.algebraMap_apply E A G]
  change algebraMap C G (algebraMap E C c) = algebraMap E G c
  exact (IsScalarTower.algebraMap_apply E C G c).symm

/-- If the local realization respects the original constants, its
constructed coefficient residue embedding respects those same constants. -/
noncomputable def coefficientRestrictionResidueFieldAlgHom
    {F : Type*} [Field F] [Algebra E F] (π : A →ₐ[E] F) [IsLocalHom π.toRingHom] :
    letI := coefficientRestrictionConstantAlgebra (A := A) (F := G) C E
    IsLocalRing.ResidueField (coefficientRestrictionValuationSubring (A := A) (F := G) C) →ₐ[E] F := by
  letI := coefficientRestrictionConstantAlgebra (A := A) (F := G) C E
  refine { coefficientRestrictionResidueFieldHom (A := A) (G := G) C π.toRingHom with commutes' := ?_ }
  intro c
  rw [IsScalarTower.algebraMap_apply E (coefficientRestrictionValuationSubring (A := A) (F := G) C)
    (IsLocalRing.ResidueField (coefficientRestrictionValuationSubring (A := A) (F := G) C))]
  change coefficientRestrictionResidueFieldHom (A := A) (G := G) C π.toRingHom
    (IsLocalRing.residue _ (algebraMap E (coefficientRestrictionValuationSubring (A := A) (F := G) C) c)) = _
  rw [coefficientRestrictionResidueFieldHom_residue, coefficientRestrictionLocalHom_constant]
  exact π.commutes c

end DimensionFourDependence
