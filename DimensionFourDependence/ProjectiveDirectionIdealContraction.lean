import DimensionFourDependence.ProjectivePointCoefficientRestriction
import DimensionFourDependence.ProjectiveBoundaryProjection

/-! # Exact lifted boundary ideals retain all original affine-direction equations -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

/-- Selecting specified projective coordinates contracts the entire
point ideal along the same variable map. -/
theorem projectiveFieldPointIdeal_coordinate_comap
    {E F σ τ : Type*} [Field E] [Field F] [Algebra E F]
    (x : σ → F) (f : τ → σ) :
    (projectiveFieldPointIdeal (E := E) x).toIdeal.comap (rename f) =
      (projectiveFieldPointIdeal (E := E) (x ∘ f)).toIdeal := by
  ext P
  change projectiveFieldPointMap (E := E) x (rename f P) = 0 ↔
    projectiveFieldPointMap (E := E) (x ∘ f) P = 0
  rw [projectiveFieldPointMap_coordinate_projection]

/-- Equality of lifted whole boundary ideals gives equality of all
original affine-direction equations after restricting constants. -/
theorem original_direction_ideal_eq_of_extended_whole_coordinate_ideal
    {E C F G σ : Type*} [Field E] [Field C] [Field F] [Field G]
    [Algebra E C] [Algebra C F] [Algebra E F] [IsScalarTower E C F]
    [Algebra C G] [Algebra E G] [IsScalarTower E C G]
    (x : Option σ → F) (y : Option σ → G)
    (hxy : (projectiveFieldPointIdeal (E := C) x).toIdeal =
      (projectiveFieldPointIdeal (E := C) y).toIdeal) :
    (projectiveFieldPointIdeal (E := E) (fun i => x (some i))).toIdeal =
      (projectiveFieldPointIdeal (E := E) (fun i => y (some i))).toIdeal := by
  have hwhole : (projectiveFieldPointIdeal (E := E) x).toIdeal =
      (projectiveFieldPointIdeal (E := E) y).toIdeal := by
    rw [← projectiveFieldPointIdeal_coefficient_comap (E := C) x,
      ← projectiveFieldPointIdeal_coefficient_comap (E := C) y, hxy]
  have h := congrArg (Ideal.comap (rename (some : σ → Option σ))) hwhole
  simpa only [projectiveFieldPointIdeal_coordinate_comap, Function.comp_def] using h

end DimensionFourDependence
