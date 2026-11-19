import DimensionFourDependence.ProjectivePrimeBaseExtension
import DimensionFourDependence.GenericDirectionTangent

/-! # Original projective equations are the exact contraction of extended-coefficient equations -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K E F G σ : Type*} [Field K] [Field E] [Field F] [Field G]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

/-- Restricting constants contracts the entire original homogeneous
point ideal, not only a selected equation or degree. -/
theorem projectiveFieldPointIdeal_coefficient_comap (x : σ → F) :
    ((projectiveFieldPointIdeal (E := E) x).toIdeal).comap (MvPolynomial.map (algebraMap K E)) =
      (projectiveFieldPointIdeal (E := K) x).toIdeal := by
  ext P
  change projectiveFieldPointMap (E := E) x (MvPolynomial.map (algebraMap K E) P) = 0 ↔
    projectiveFieldPointMap (E := K) x P = 0
  rw [projectiveFieldPointMap_coefficient_extension]

variable [Algebra K G] [Algebra E G] [IsScalarTower K E G]

/-- Inclusion of complete projective equation ideals remains inclusion
over the original constants, with the same two coordinate tuples. -/
theorem projectiveFieldPointIdeal_le_of_extended_coefficients (x : σ → F) (y : σ → G)
    (hle : (projectiveFieldPointIdeal (E := E) x).toIdeal ≤
      (projectiveFieldPointIdeal (E := E) y).toIdeal) :
    (projectiveFieldPointIdeal (E := K) x).toIdeal ≤
      (projectiveFieldPointIdeal (E := K) y).toIdeal := by
  rw [← projectiveFieldPointIdeal_coefficient_comap (E := E) x,
    ← projectiveFieldPointIdeal_coefficient_comap (E := E) y]
  exact Ideal.comap_mono hle

end DimensionFourDependence
