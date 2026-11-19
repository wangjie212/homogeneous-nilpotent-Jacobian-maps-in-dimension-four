import DimensionFourDependence.Nilpotent

/-! # The determinant and second trace identity of the Segre ruling restriction matrix -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 3000000

variable {R : Type*} [CommRing R]

/-- Equation (5.2), with the derivative entries kept as independent
symbols so the two matrix identities hold over every commutative ring. -/
def segreRulingRestrictionMatrix (j k f h df dh A dA : R) : Matrix (Fin 3) (Fin 3) R :=
  !![k * f, df + j * A * f, j * h * f;
     k * h, dh + f + j * A * h, j * h ^ 2;
     0, dA + A ^ 2, f + A * h]

/-- The dominance factor is the original Wronskian after writing
`g = h + s*f` and differentiating with respect to `s`. -/
def segreRulingDominanceFactor (f h df dh : R) : R := f * dh - h * df + f ^ 2

/-- The determinant retains the exact primitive degree and dominance
factors; no derivative or nilpotence identity is assumed. -/
theorem segre_ruling_restriction_matrix_det (j k f h df dh A dA : R) :
    (segreRulingRestrictionMatrix j k f h df dh A dA).det =
      k * segreRulingDominanceFactor f h df dh * (f + A * h) := by
  simp [Matrix.det_fin_three, segreRulingRestrictionMatrix, segreRulingDominanceFactor]
  ring

/-- Twice the sum of principal two-by-two minors, including the term
that vanishes only after the determinant has forced `f + A*h = 0`. -/
theorem segre_ruling_restriction_matrix_second_trace (j k f h df dh A dA : R) :
    Matrix.trace (segreRulingRestrictionMatrix j k f h df dh A dA) ^ 2 -
      Matrix.trace (segreRulingRestrictionMatrix j k f h df dh A dA *
        segreRulingRestrictionMatrix j k f h df dh A dA) =
      2 * (k * segreRulingDominanceFactor f h df dh - j * h ^ 2 * (dA + A ^ 2) +
        (k * f + dh + f + j * A * h) * (f + A * h)) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, segreRulingRestrictionMatrix,
    segreRulingDominanceFactor, Fin.sum_univ_succ]
  ring

/-- Dominance in the coordinates of the paper has exactly the factor
used by the determinant computation, without discarding the Euler term. -/
theorem segre_ruling_dominance_factor_eq_wronskian
    (f g s df dg : R) :
    segreRulingDominanceFactor f (g - s * f) df (dg - f - s * df) = f * dg - g * df := by
  dsimp only [segreRulingDominanceFactor]
  ring

end DimensionFourDependence
