import DimensionFourDependence.AffineQuadraticShearInvariants
import DimensionFourDependence.AffineTangentNormalization

/-! # Independent affine tangent directions construct a quadratic composite parameter

The actual two tangent equations construct normalized lifts, closedness,
the quadratic potential and the full polynomial invariant. Both the
explicit nonzero determinant and the intrinsic independent projected
pair formulations are provided.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K]

/-- Independent projected tangent equations of P construct Q of degree
at most two and a nonconstant F with the entire identity P=F(w-Q). -/
theorem independent_projected_affine_tangents_construct_quadratic_composite_parameter
    (P : MvPolynomial (Fin 3) K) (hPw : pderiv (2 : Fin 3) P ≠ 0)
    (u v : Fin 2 → K) (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0)
    (b c : Fin 3 → K) (hu : affineProjectedTangentAction u b P = 0)
    (hv : affineProjectedTangentAction v c P = 0) :
    ∃ (Q : MvPolynomial (Fin 2) K) (F : Polynomial K), Q.totalDegree ≤ 2 ∧ 0 < F.natDegree ∧
      P = Polynomial.aeval (X 2 - rename Fin.castSucc Q) F := by
  obtain ⟨b', c', hx, hz⟩ := independent_projected_affine_tangents_construct_normalized_lifts P u v hdet b c hu hv
  exact invariant_affine_tangent_lifts_construct_quadratic_composite_parameter P hPw b' c' hx hz

/-- The intrinsic independent projected direction pair supplies its
nonzero minor internally, before constructing the full quadratic composite. -/
theorem independent_affine_tangent_fields_construct_quadratic_composite_parameter
    (P : MvPolynomial (Fin 3) K) (hPw : pderiv (2 : Fin 3) P ≠ 0)
    (u v : Fin 2 → K) (hdir : LinearIndependent K ![u, v])
    (b c : Fin 3 → K) (hu : affineProjectedTangentAction u b P = 0)
    (hv : affineProjectedTangentAction v c P = 0) :
    ∃ (Q : MvPolynomial (Fin 2) K) (F : Polynomial K), Q.totalDegree ≤ 2 ∧ 0 < F.natDegree ∧
      P = Polynomial.aeval (X 2 - rename Fin.castSucc Q) F := by
  let M : Matrix (Fin 2) (Fin 2) K := ![u, v]
  have hrows : LinearIndependent K M.row := hdir
  have hunit : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hunit).ne_zero
  have hdetformula : M.det = u 0 * v 1 - u 1 * v 0 := by
    rw [Matrix.det_fin_two]
    rfl
  have hminor : u 0 * v 1 - u 1 * v 0 ≠ 0 := by
    rw [hdetformula] at hdet
    exact hdet
  exact independent_projected_affine_tangents_construct_quadratic_composite_parameter P hPw u v hminor b c hu hv

end DimensionFourDependence
