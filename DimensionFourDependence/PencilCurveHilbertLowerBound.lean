import DimensionFourDependence.PencilCoefficientCurveField
import DimensionFourDependence.ExtendedOwnCoordinateFieldGeneration
import DimensionFourDependence.ProjectivePointTranscendenceLowerBound

/-! # The actual normalized pencil curve has positive linear Hilbert growth -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

/-- Original field generators still generate after compatibly
enlarging their coefficient field inside the same source field. -/
theorem field_generators_adjoin_top_after_extending_coefficients
    {E C F σ : Type*} [Field E] [Field C] [Field F]
    [Algebra E C] [Algebra C F] [Algebra E F] [IsScalarTower E C F]
    (x : σ → F) (hx : IntermediateField.adjoin E (Set.range x) = ⊤) :
    IntermediateField.adjoin C (Set.range x) = ⊤ := by
  let T := IntermediateField.adjoin C (Set.range x)
  have hle : IntermediateField.adjoin E (Set.range x) ≤ T.restrictScalars E := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin C _ ⟨i, rfl⟩
  rw [hx] at hle
  apply top_unique
  intro y _hy
  exact hle (by trivial)

/-- A transcendental pencil on a genuine surface retains a
nonalgebraic curve direction after taking its full relative coefficient closure. -/
theorem pencil_coefficient_curve_relative_trdeg_ne_zero
    {E F : Type u} [Field E] [Field F] [Algebra E F]
    (t : F) (ht : Transcendental E t) (hF : Algebra.trdeg E F = 2) :
    Algebra.trdeg (pencilCoefficientCurveField (E := E) t) F ≠ 0 := by
  let C := pencilCoefficientCurveField (E := E) t
  letI : IsScalarTower E C F := pencilCoefficientCurveField_scalarTower t
  letI : FaithfulSMul E C :=
    (faithfulSMul_iff_algebraMap_injective E C).mpr (algebraMap E C).injective
  letI : FaithfulSMul C F :=
    (faithfulSMul_iff_algebraMap_injective C F).mpr (algebraMap C F).injective
  intro hz
  have hsum := trdeg_add_eq (A := F) E C
  rw [pencilCoefficientCurveField_trdeg_one t ht, hz, add_zero, hF] at hsum
  norm_num at hsum

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "F₀" => (N).functionField
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance pencilCurveHilbertLowerBoundIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance pencilCurveHilbertLowerBoundAlgebra : Algebra E (F₀) :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- A nonconstant actual pencil has a transcendental original
coordinate over its own full relatively closed coefficient curve. -/
theorem actual_normalized_surface_pencil_has_transcendental_coordinate
    (hGauss : gaussImageDimension H I = 1) (t : F₀) (ht : Transcendental E t) :
    ∃ i : Fin 4, Transcendental (pencilCoefficientCurveField (E := E) t) ((w) i) := by
  let C := pencilCoefficientCurveField (E := E) t
  letI : IsScalarTower E C (F₀) := pencilCoefficientCurveField_scalarTower t
  let x : Fin 3 → F₀ := fun i => (w) ((finSuccEquiv' (0 : Fin 4)).symm (some i))
  have hgen : IntermediateField.adjoin C (Set.range x) = ⊤ :=
    field_generators_adjoin_top_after_extending_coefficients x
      (extendedClosedGaussNormalization_original_affine_field_top H I E hH e)
  have htr : Algebra.trdeg C (F₀) ≠ 0 := pencil_coefficient_curve_relative_trdeg_ne_zero t ht
    (extendedClosedGaussNormalization_functionField_trdeg_two H I E hH e hGauss)
  obtain ⟨i, hi⟩ := exists_transcendental_coordinate x hgen htr
  exact ⟨(finSuccEquiv' (0 : Fin 4)).symm (some i), hi⟩

/-- Every homogeneous degree of the actual generic pencil curve
has at least n+1 independent sections in the original source coordinates. -/
theorem actual_normalized_surface_pencil_curve_hilbert_lower_bound
    (hGauss : gaussImageDimension H I = 1) (t : F₀) (ht : Transcendental E t) (n : ℕ) :
    n + 1 ≤ projectiveHilbertFunction
      (projectiveFieldPointIdeal (E := pencilCoefficientCurveField (E := E) t) (w)).toIdeal n := by
  obtain ⟨i, hi⟩ := actual_normalized_surface_pencil_has_transcendental_coordinate H I E hH e hGauss t ht
  exact projective_point_hilbert_lower_bound_of_unit_frame_and_transcendental
    (w) 0 i (extendedClosedGaussNormalizationHyperplaneWeight_zero H I E hH e) hi n

end DimensionFourDependence
