import DimensionFourDependence.CovectorPlaneFrameExclusion

/-! # A fixed-plane source linear form pulls back to an actual nonzero original covector -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- A nonzero fixed-plane linear form in the new source prime
constructs a nonzero original constant covector in the contracted
prime. Its forward pullback lies in the actual fixed-coordinate
polynomial ring. All coefficient and inverse-matrix identities are
retained, without choosing a point on the prime. -/
theorem fixed_plane_linear_form_constructs_nonzero_inverse_frame_covector
    (T S : Matrix (Fin 4) (Fin 4) K) (hTS : T * S = 1) (hST : S * T = 1)
    (Q : Ideal R₀) (α β : K) (hab : α ≠ 0 ∨ β ≠ 0)
    (hlinear : C α * X 0 + C β * X 3 ∈ Q) :
    ∃ w : Fin 4 → K, w ≠ 0 ∧
      linearFormPolynomial w ∈ Q.comap (matrixPolynomialCoordinateEquiv T S hTS hST).toRingHom ∧
      linearPolynomialPullback T (linearFormPolynomial w) ∈ Set.range (fixedPlaneCoefficientMap K) := by
  let c : Fin 4 → K := ![α, 0, 0, β]
  let w : Fin 4 → K := c ᵥ* S
  have hw0 : w ≠ 0 := by
    intro hz
    have he := congrArg (fun v : Fin 4 → K => v ᵥ* T) hz
    have hc0 : c = 0 := by
      simpa only [w, Matrix.vecMul_vecMul, hST, Matrix.vecMul_one, Matrix.zero_vecMul] using he
    have hα : α = 0 := by simpa only [c, Matrix.cons_val_zero, Pi.zero_apply] using congrFun hc0 0
    have hβ : β = 0 := by simpa [c] using congrFun hc0 3
    exact hab.elim (fun h => h hα) (fun h => h hβ)
  have hL : linearFormPolynomial c = C α * X 0 + C β * X 3 := by
    simp [linearFormPolynomial, c, Fin.sum_univ_succ]
  have hback : linearFormPolynomial w = linearPolynomialPullback S (linearFormPolynomial c) := by
    rw [linearPolynomialPullback_linear_form]
    rfl
  have hforward : linearPolynomialPullback T (linearFormPolynomial w) = C α * X 0 + C β * X 3 := by
    rw [hback, matrix_linear_polynomial_substitution_inverse S T hST, hL]
  refine ⟨w, hw0, ?_, ?_⟩
  · change linearPolynomialPullback T (linearFormPolynomial w) ∈ Q
    rw [hforward]
    exact hlinear
  · refine ⟨C α * X (0 : Fin 2) + C β * X (1 : Fin 2), ?_⟩
    rw [hforward]
    simp [fixedPlaneCoefficientMap]

end DimensionFourDependence
