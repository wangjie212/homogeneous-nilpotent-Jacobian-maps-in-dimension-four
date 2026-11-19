import DimensionFourDependence.HomogenizedTernaryNormalForm

/-! # The exact affine chart and fixed-degree reconstruction of Proposition 6.6 -/

namespace DimensionFourDependence.TernaryNormalForm

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "t" => (X (Fin.last 3))
local notation "D" => (lastCoordinateDehomogenize (K := K) (n := 3))

theorem dehomogenize_normal_quadratic4 :
    D (quadratic4 (K := K)) = (X 1 + X 0 ^ 2 : R₃) := by
  have hx : D (X 0) = X 0 := lastCoordinateDehomogenize_X_castSucc (0 : Fin 3)
  have hy : D (X 1) = X 1 := lastCoordinateDehomogenize_X_castSucc (1 : Fin 3)
  simp only [quadratic4, map_add, map_mul, map_pow, lastCoordinateDehomogenize_X_last,
    hx, hy, one_mul]

theorem dehomogenize_normal_numerator4 (P : Polynomial K) :
    D (numerator4 P) = Polynomial.aeval (X 1 + X 0 ^ 2 : R₃) P := by
  unfold numerator4
  rw [homogeneousParameterPolynomialValue_algHom, dehomogenize_normal_quadratic4,
    map_pow, lastCoordinateDehomogenize_X_last, one_pow]
  exact Polynomial.aeval_homogenize_of_eq_one le_rfl _ rfl

theorem dehomogenize_normal_perturbation4
    (P : Polynomial K) (d : ℕ) (i : Fin 3) :
    D (perturbation4 P d i.castSucc) = perturbation3 P i := by
  have hx : D (X 0) = X 0 := lastCoordinateDehomogenize_X_castSucc (0 : Fin 3)
  have hz : D (X 2) = X 2 := lastCoordinateDehomogenize_X_castSucc (2 : Fin 3)
  have ht : D (X (3 : Fin 4) : R₄) = 1 := lastCoordinateDehomogenize_X_last
  have h₂ : D (2 : R₄) = 2 := map_ofNat D 2
  fin_cases i <;>
    simp [perturbation4, perturbation3, q4, correction4, dehomogenize_normal_numerator4,
      hx, hz, ht, h₂, map_add, map_sub, map_mul, map_pow]

/-- The polynomial formula in four variables is the prescribed
degree homogenization of every active canonical ternary coordinate. -/
theorem perturbation4_eq_homogenize_perturbation3
    (P : Polynomial K) {d : ℕ} (hm : 0 < P.natDegree) (hd : 4 * P.natDegree ≤ d) :
    perturbation4 P d = Fin.lastCases 0 (fun i : Fin 3 => lastCoordinateHomogenize (perturbation3 P i) d) := by
  have hh (i : Fin 3) := lastCoordinateHomogenize_dehomogenize _
    (perturbation4_isHomogMap P hm hd i.castSucc)
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.lastCases_last]
    rfl
  · rw [Fin.lastCases_castSucc, ← dehomogenize_normal_perturbation4 P d i]
    exact (hh i).symm

end DimensionFourDependence.TernaryNormalForm
