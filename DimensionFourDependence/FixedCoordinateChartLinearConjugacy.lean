import DimensionFourDependence.LastCoordinateDehomogenization
import DimensionFourDependence.FixedCovectorCoordinateChoice

/-! # Constant conjugation of the active variables commutes with the final-coordinate chart -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 2800000

variable {K : Type*} [Field K] {n : ℕ}
local notation "D" => (lastCoordinateDehomogenize (K := K) (n := n))

theorem lastCoordinateDehomogenize_rename_active (p : MvPolynomial (Fin n) K) :
    D (rename Fin.castSucc p) = p := by
  have he : (D).comp (rename Fin.castSucc) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, rename_X, AlgHom.id_apply] using
      lastCoordinateDehomogenize_X_castSucc (K := K) i
  exact AlgHom.congr_fun he p

theorem lastCoordinateDehomogenize_vertexPreserving_pullback
    (T : Matrix (Fin n) (Fin n) K) (p : MvPolynomial (Fin (n + 1)) K) :
    D (linearPolynomialPullback (vertexPreservingMatrix T) p) = linearPolynomialPullback T (D p) := by
  have he : (D).comp (aeval (linearPolynomialMap (vertexPreservingMatrix T))) =
      (aeval (linearPolynomialMap T)).comp D := by
    apply MvPolynomial.algHom_ext
    intro j
    change D (linearPolynomialPullback (vertexPreservingMatrix T) (X j)) = linearPolynomialPullback T (D (X j))
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [vertexPreservingMatrix_vertex_pullback, lastCoordinateDehomogenize_X_last]
      exact (map_one (aeval (linearPolynomialMap T))).symm
    · rw [lastCoordinateDehomogenize_X_castSucc, ← rename_X]
      rw [vertexPreservingMatrix_transverse_pullback, lastCoordinateDehomogenize_rename_active]
  exact AlgHom.congr_fun he p

/-- A constant linear change of active source and target coordinates
has the same action before and after setting the last coordinate to one. -/
theorem lastCoordinateDehomogenize_vertexPreserving_conjugate
    (T S : Matrix (Fin n) (Fin n) K)
    (H : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (i : Fin n) :
    D (linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H i.castSucc) =
      linearPolynomialConjugate T S (fun j => D (H j.castSucc)) i := by
  simp only [linearPolynomialConjugate, map_sum, map_mul, lastCoordinateDehomogenize_C,
    lastCoordinateDehomogenize_vertexPreserving_pullback]
  rw [Fin.sum_univ_castSucc]
  have hz : vertexPreservingMatrix S i.castSucc (Fin.last n) = 0 := by simp [vertexPreservingMatrix]
  simp only [vertexPreservingMatrix_castSucc, hz, map_zero, zero_mul, add_zero]

theorem vertexPreserving_conjugate_last_zero
    (T S : Matrix (Fin n) (Fin n) K)
    (H : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hz : H (Fin.last n) = 0) :
    linearPolynomialConjugate (vertexPreservingMatrix T) (vertexPreservingMatrix S) H (Fin.last n) = 0 := by
  simp [linearPolynomialConjugate, vertexPreservingMatrix_last_row, hz,
    linearPolynomialPullback, apply_ite, Finset.sum_ite_eq']

end DimensionFourDependence
