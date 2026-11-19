import DimensionFourDependence.CoefficientRestrictionResidueRealization
import DimensionFourDependence.ProjectivePointTranscendenceLowerBound
import DimensionFourDependence.CurveHilbertComparisonExistence

/-! # Algebraic coefficient residue preserves positive curve degree at specialization -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {E A F : Type*} [Field E] [CommRing A] [IsDomain A] [ValuationRing A]
  [Field F] [Algebra E A] [Algebra A F] [IsFractionRing A F]
  [Algebra E F] [IsScalarTower E A F]
  (C : Type*) [Field C] [Algebra C F] [Algebra E C] [IsScalarTower E C F]

/-- The restricted coefficient residue field and the actual source
residue field retain exactly the same original constant-field action. -/
theorem coefficientRestrictionResidueAlgebra_constant_scalarTower :
    letI := coefficientRestrictionConstantAlgebra (A := A) (F := F) C E
    letI := coefficientRestrictionResidueAlgebra (A := A) (F := F) C
    IsScalarTower E
      (IsLocalRing.ResidueField (coefficientRestrictionValuationSubring (A := A) (F := F) C))
      (IsLocalRing.ResidueField A) := by
  let V := coefficientRestrictionValuationSubring (A := A) (F := F) C
  letI := coefficientRestrictionConstantAlgebra (A := A) (F := F) C E
  letI := coefficientRestrictionResidueAlgebra (A := A) (F := F) C
  apply IsScalarTower.of_algebraMap_eq
  intro c
  rw [IsScalarTower.algebraMap_apply E V (IsLocalRing.ResidueField V)]
  change algebraMap E (IsLocalRing.ResidueField A) c =
    coefficientRestrictionResidueHom (A := A) (F := F) C
      (IsLocalRing.residue V (algebraMap E V c))
  rw [coefficientRestrictionResidueHom_residue, coefficientRestrictionLocalHom_constant]
  exact IsScalarTower.algebraMap_apply E A (IsLocalRing.ResidueField A) c

/-- An original residue parameter stays transcendental after the
constructed restricted coefficient residue field, when that field is
algebraic over the original constants. -/
theorem coefficient_restriction_residue_transcendental_of_algebraic_constants
    (halg : letI := coefficientRestrictionConstantAlgebra (A := A) (F := F) C E
      Algebra.IsAlgebraic E (IsLocalRing.ResidueField
        (coefficientRestrictionValuationSubring (A := A) (F := F) C)))
    (x : IsLocalRing.ResidueField A) (hx : Transcendental E x) :
    letI := coefficientRestrictionResidueAlgebra (A := A) (F := F) C
    Transcendental
      (IsLocalRing.ResidueField (coefficientRestrictionValuationSubring (A := A) (F := F) C)) x := by
  let V := coefficientRestrictionValuationSubring (A := A) (F := F) C
  letI := coefficientRestrictionConstantAlgebra (A := A) (F := F) C E
  letI := coefficientRestrictionResidueAlgebra (A := A) (F := F) C
  letI := coefficientRestrictionResidueAlgebra_constant_scalarTower (E := E) (A := A) (F := F) C
  letI : Algebra.IsAlgebraic E (IsLocalRing.ResidueField V) := halg
  intro h
  exact hx (h.restrictScalars E)

/-- A genuine original residue coordinate constructs the specialized
curve's own positive Hilbert degree. The coefficient residue field,
its scalar compatibility and the upper bound are all constructed. -/
theorem source_valuation_coefficient_residue_curve_degree_exists
    {σ : Type*} [Finite σ]
    (halg : letI := coefficientRestrictionConstantAlgebra (A := A) (F := F) C E
      Algebra.IsAlgebraic E (IsLocalRing.ResidueField
        (coefficientRestrictionValuationSubring (A := A) (F := F) C)))
    (x : σ → F) (s : F) (hs : s ≠ 0) (z : σ → A)
    (hz : ∀ i, algebraMap A F (z i) = s * x i)
    (a i : σ) (ha : z a = 1) (hi : Transcendental E (IsLocalRing.residue A (z i)))
    {D : ℕ} (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C) x).toIdeal D) :
    letI := coefficientRestrictionResidueAlgebra (A := A) (F := F) C
    ∃ D' : ℕ, D' ≤ D ∧ HasCurveHilbertDegree
      (projectiveFieldPointIdeal
        (E := IsLocalRing.ResidueField (coefficientRestrictionValuationSubring (A := A) (F := F) C))
        (fun j => IsLocalRing.residue A (z j))).toIdeal D' := by
  letI := coefficientRestrictionResidueAlgebra (A := A) (F := F) C
  have htr := coefficient_restriction_residue_transcendental_of_algebraic_constants
    (E := E) (A := A) (F := F) C halg _ hi
  have hframe : IsLocalRing.residue A (z a) = 1 := by rw [ha, map_one]
  apply exists_curve_hilbert_degree_of_hilbert_comparison _
    (projectiveFieldPointIdeal
      (E := IsLocalRing.ResidueField (coefficientRestrictionValuationSubring (A := A) (F := F) C))
      (fun j => IsLocalRing.residue A (z j))).isHomogeneous _ hD
  · exact fun n => projective_point_hilbert_lower_bound_of_unit_frame_and_transcendental
      (fun j => IsLocalRing.residue A (z j)) a i hframe htr n
  · intro n
    have hb := source_valuation_coefficient_restriction_hilbert_bound (A := A) (F := F) C z n
    have he : (fun j => algebraMap A F (z j)) = fun j => s * x j := funext hz
    rwa [he, projectiveFieldPointIdeal_scale x s hs] at hb

end DimensionFourDependence
