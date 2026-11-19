import DimensionFourDependence.FixedConeCoordinateConjugacy
import DimensionFourDependence.ProjectiveSourceSections

/-! # The complete cone parameter is polynomial on its fixed-coordinate chart

The exact denominator power survives the actual coordinate conjugacy.
Dehomogenizing its homogeneous numerator constructs a polynomial in the
three free affine coordinates, with the same original source-field value.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The exact fixed-linear denominator becomes the corresponding
coordinate power under the same source-field change as the cone forms. -/
theorem fixed_linear_denominator_conjugate_parameter_value
    (T S : Matrix (Fin 3) (Fin 3) K)
    (hTS : vertexPreservingMatrix T * vertexPreservingMatrix S = 1)
    (hST : vertexPreservingMatrix S * vertexPreservingMatrix T = 1)
    (t : S₀) (p : R₀) (q : MvPolynomial (Fin 3) K) (c : Fin 3 → K) (γ : K) (D : ℕ)
    (ht : t = algebraMap R₀ S₀ p / algebraMap R₀ S₀ (rename Fin.castSucc q))
    (hq : q = C γ * linearFormPolynomial c ^ D)
    (j : Fin 3) (hlinear : linearPolynomialPullback (vertexPreservingMatrix T)
      (rename Fin.castSucc (linearFormPolynomial c)) = X j.castSucc) :
    matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST t =
      algebraMap R₀ S₀ (linearPolynomialPullback (vertexPreservingMatrix T) p) /
        (algebraMap K S₀ γ * rationalCoordinate (K := K) j.castSucc ^ D) := by
  let f := matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST
  have hy : f (algebraMap R₀ S₀ (rename Fin.castSucc (linearFormPolynomial c))) =
      rationalCoordinate (K := K) j.castSucc := by
    rw [matrixSourceFractionEquiv_polynomial, hlinear]
    rfl
  have hqvalue : algebraMap R₀ S₀ (rename Fin.castSucc q) =
      algebraMap K S₀ γ * (algebraMap R₀ S₀ (rename Fin.castSucc (linearFormPolynomial c))) ^ D := by
    rw [hq, map_mul, map_pow, rename_C, map_mul, map_pow]
    rfl
  change f t = _
  rw [ht, map_div₀, hqvalue, map_mul, map_pow, hy, AlgEquiv.commutes,
    matrixSourceFractionEquiv_polynomial]

/-- A homogeneous numerator over a scalar coordinate-power denominator
constructs the complete polynomial parameter on that affine source chart. -/
theorem homogeneous_coordinate_power_parameter_constructs_chart_polynomial
    (s : Fin 4 ≃ Option (Fin 3)) (t : S₀) (p : R₀) (γ : K) (D : ℕ)
    (hp : p.IsHomogeneous D)
    (ht : t = algebraMap R₀ S₀ p /
      (algebraMap K S₀ γ * rationalCoordinate (K := K) (s.symm none) ^ D)) :
    ∃ P : MvPolynomial (Fin 3) K, P.totalDegree ≤ D ∧
      t = aeval (closedGaussPencilChartPoint (K := K) s) P := by
  let P := C γ⁻¹ * projectiveSourceDehomogenize s p
  have hvalue : aeval (closedGaussPencilChartPoint (K := K) s)
      (projectiveSourceDehomogenize s p) =
        algebraMap R₀ S₀ p / rationalCoordinate (K := K) (s.symm none) ^ D := by
    rw [← projectiveSourceFullChartCoordinateEquiv_source]
    change (projectiveSourceSectionHom s p : S₀) = _
    exact projectiveSourceSectionHom_homogeneous_value s p hp
  refine ⟨P, ?_, ?_⟩
  · calc
      P.totalDegree ≤ (projectiveSourceDehomogenize s p).totalDegree := by
        exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C, zero_add, le_refl])
      _ ≤ p.totalDegree := projectiveSourceDehomogenize_totalDegree s p
      _ ≤ D := by
        by_cases hz : p = 0
        · rw [hz]; simp
        · exact (hp.totalDegree hz).le
  · dsimp only [P]
    rw [map_mul, aeval_C, hvalue, ht]
    simp only [map_inv₀, div_eq_mul_inv, _root_.mul_inv_rev]
    ring

/-- A polynomial chart value representing a transcendental actual
parameter is necessarily nonconstant. -/
theorem transcendental_chart_parameter_polynomial_positive_degree
    (x : Fin 3 → S₀) (t : S₀) (ht : Transcendental K t)
    (P : MvPolynomial (Fin 3) K) (hvalue : t = aeval x P) :
    0 < P.totalDegree := by
  by_contra! hzero
  have hP := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hzero)
  apply ht
  rw [hvalue, hP, aeval_C]
  exact isAlgebraic_algebraMap _

/-- The parameter on the fixed-linear chart after actual conjugacy
is a constructed polynomial of degree at most the original denominator
degree, in the same actual three free coordinate ratios. -/
theorem fixed_linear_parameter_conjugacy_constructs_affine_polynomial
    (T S : Matrix (Fin 3) (Fin 3) K)
    (hTS : vertexPreservingMatrix T * vertexPreservingMatrix S = 1)
    (hST : vertexPreservingMatrix S * vertexPreservingMatrix T = 1)
    (t : S₀) (p : R₀) (q : MvPolynomial (Fin 3) K) (c : Fin 3 → K) (γ : K) (D : ℕ)
    (hp : p.IsHomogeneous D)
    (ht : t = algebraMap R₀ S₀ p / algebraMap R₀ S₀ (rename Fin.castSucc q))
    (hq : q = C γ * linearFormPolynomial c ^ D)
    (j : Fin 3) (hlinear : linearPolynomialPullback (vertexPreservingMatrix T)
      (rename Fin.castSucc (linearFormPolynomial c)) = X j.castSucc)
    (s : Fin 4 ≃ Option (Fin 3)) (hs : s.symm none = j.castSucc) :
    ∃ P : MvPolynomial (Fin 3) K, P.totalDegree ≤ D ∧
      matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST t =
        aeval (closedGaussPencilChartPoint (K := K) s) P := by
  apply homogeneous_coordinate_power_parameter_constructs_chart_polynomial s
    (matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST t)
    (linearPolynomialPullback (vertexPreservingMatrix T) p) γ D
    (linearPolynomialPullback_homogeneous _ p hp)
  rw [hs]
  exact fixed_linear_denominator_conjugate_parameter_value T S hTS hST t p q c γ D ht hq j hlinear

/-- The second-coordinate affine source chart has exactly the original
x/y, z/y, w/y coordinate order used after (4.10). -/
theorem second_coordinate_cone_chart_point :
    closedGaussPencilChartPoint (K := K) (finSuccEquiv' (1 : Fin 4)) =
      ![rationalCoordinate (K := K) (0 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4),
        rationalCoordinate (K := K) (2 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4),
        rationalCoordinate (K := K) (3 : Fin 4) / rationalCoordinate (K := K) (1 : Fin 4)] := by
  funext i
  fin_cases i <;> rfl

end DimensionFourDependence
