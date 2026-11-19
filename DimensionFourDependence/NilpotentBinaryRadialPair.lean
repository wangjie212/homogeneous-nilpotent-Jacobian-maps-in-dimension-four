import DimensionFourDependence.Nilpotent

/-! # Nilpotence excludes a nonzero radial first pair directly in the polynomial source ring -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 2000000

/-- A cleared-denominator eigenvector equation for a nilpotent matrix
forces its numerator eigenvalue to vanish. This works in the original
domain, without choosing a rational denominator or an eigenvector field. -/
theorem scaled_eigenvalue_zero_of_nilpotent
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) R) (hN : IsNilpotent N)
    (v : Fin n → R) (hv : v ≠ 0) (a b : R)
    (he : a • (v ᵥ* N) = b • v) : b = 0 := by
  have hp (j : ℕ) : a ^ j • (v ᵥ* N ^ j) = b ^ j • v := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        _ = a • ((a ^ j • (v ᵥ* N ^ j)) ᵥ* N) := by
          simp only [pow_succ, mul_smul, smul_vecMul, Matrix.vecMul_vecMul]
          rw [smul_comm]
        _ = a • ((b ^ j • v) ᵥ* N) := by rw [ih]
        _ = b ^ j • (a • (v ᵥ* N)) := by rw [smul_vecMul, smul_comm]
        _ = _ := by rw [he, ← mul_smul, pow_succ]
  obtain ⟨k, hk⟩ := hN
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hv
  have hz := congrFun (hp k) i
  rw [hk] at hz
  simp only [Matrix.vecMul_zero, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero] at hz
  have hb : b ^ k = 0 := (mul_eq_zero.mp hz.symm).resolve_right hi
  exact isNilpotent_iff_eq_zero.mp ⟨k, hb⟩

variable {K : Type*} [Field K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- An actual polynomial map with a nilpotent Jacobian cannot have a
nonzero first pair proportional to (X0,X1). Differentiation constructs
the original polynomial scaled left eigenvector. -/
theorem nilpotent_binary_radial_output_pair_zero
    (H : Fin 4 → R₀) (hN : IsNilpotent (jac H))
    (hcross : X 0 * H 1 = X 1 * H 0) : H 0 = 0 ∧ H 1 = 0 := by
  let v : Fin 4 → R₀ := ![-X 1, X 0, 0, 0]
  have hv : v ≠ 0 := by
    intro hz
    exact MvPolynomial.X_ne_zero (R := K) (0 : Fin 4) (congrFun hz 1)
  have hrow : v ᵥ* jac H = ![-H 1, H 0, 0, 0] := by
    funext j
    have he := congrArg (pderiv j) hcross
    fin_cases j <;>
      simp [v, Matrix.vecMul, dotProduct, jac, Fin.sum_univ_succ,
        pderiv_mul, pderiv_X] at he ⊢ <;> linear_combination he
  have hscaled : (X 0 : R₀) • (v ᵥ* jac H) = H 0 • v := by
    rw [hrow]
    funext j
    fin_cases j <;> simp [v, Pi.smul_apply, smul_eq_mul]
    · linear_combination hcross
    · ring
  have h0 := scaled_eigenvalue_zero_of_nilpotent (jac H) hN v hv (X 0) (H 0) hscaled
  have h1 : H 1 = 0 := by
    rw [h0, mul_zero] at hcross
    exact (mul_eq_zero.mp hcross).resolve_left (MvPolynomial.X_ne_zero (0 : Fin 4))
  exact ⟨h0, h1⟩

end DimensionFourDependence
