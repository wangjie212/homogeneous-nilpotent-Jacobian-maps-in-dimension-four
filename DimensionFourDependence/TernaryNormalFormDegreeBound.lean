import DimensionFourDependence.HomogenizedTernaryNormalForm
import DimensionFourDependence.MonicHypersurfaceProjection
import DimensionFourDependence.LinearPolynomialConjugacy

/-! # An affine degree bound on the canonical family forces `4 deg P ≤ d` -/

namespace DimensionFourDependence.TernaryNormalForm

open Matrix MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]
local notation "R₃" => MvPolynomial (Fin 3) K

/-- Specializing the square coordinate to the x axis has univariate
degree exactly `4 deg P`. Therefore no affine total-degree bound can
be smaller than the one used in Proposition 6.6. -/
theorem canonical_ternary_degree_lower_bound (P : Polynomial K) :
    4 * P.natDegree ≤ (perturbation3 P 2).totalDegree := by
  let s : Fin 3 → Polynomial K := ![Polynomial.X, 0, 0]
  have hs (i : Fin 3) : (s i).natDegree ≤ 1 := by fin_cases i <;> simp [s]
  have he : (aeval s) (perturbation3 P 2) = (P.comp (Polynomial.X ^ 2)) ^ 2 := by
    change (aeval s) ((Polynomial.aeval (X 1 + X 0 ^ 2 : R₃) P) ^ 2) = _
    rw [map_pow, ← Polynomial.aeval_algHom_apply]
    simp only [map_add, map_pow, aeval_X]
    change (Polynomial.aeval (0 + Polynomial.X ^ 2) P) ^ 2 = _
    rw [zero_add]
    rfl
  have h := polynomial_natDegree_aeval_le_totalDegree s hs (perturbation3 P 2)
  rw [he, Polynomial.natDegree_pow, Polynomial.natDegree_comp, Polynomial.natDegree_pow,
    Polynomial.natDegree_X] at h
  omega

/-- A constant linear source and target change respects any common
degree bound on the coordinates. -/
theorem linearPolynomialConjugate_totalDegree_le {n d : ℕ}
    (T S : Matrix (Fin n) (Fin n) K) (H : Fin n → MvPolynomial (Fin n) K)
    (hH : ∀ i, (H i).totalDegree ≤ d) (i : Fin n) :
    (linearPolynomialConjugate T S H i).totalDegree ≤ d := by
  have hlin (j : Fin n) : (linearPolynomialMap T j).totalDegree ≤ 1 := by
    by_cases h : linearPolynomialMap T j = 0
    · simp [h]
    · exact ((linearPolynomialMap_homogeneous T j).totalDegree h).le
  unfold linearPolynomialConjugate
  apply totalDegree_finsetSum_le
  intro j _
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact (totalDegree_aeval_le_of_linear _ hlin _).trans (hH j)

theorem canonical_ternary_degree_bound_of_linear_normal_form {d : ℕ}
    (P : Polynomial K) (H : Fin 3 → R₃) (T S : Matrix (Fin 3) (Fin 3) K)
    (hH : ∀ i, (H i).totalDegree ≤ d) (hn : linearPolynomialConjugate T S H = perturbation3 P) :
    4 * P.natDegree ≤ d := by
  apply (canonical_ternary_degree_lower_bound P).trans
  rw [← hn]
  exact linearPolynomialConjugate_totalDegree_le T S H hH 2

end DimensionFourDependence.TernaryNormalForm
