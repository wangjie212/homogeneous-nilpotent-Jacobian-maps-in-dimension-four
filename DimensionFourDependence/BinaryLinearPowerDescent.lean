import DimensionFourDependence.BinaryLinearPowerHessian

/-! # An actual binary linear-times-power factorization descends to its original field -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type*} [Field K] [Field E]

/-- Once the repeated linear factor is normalized over the original
field, its whole complementary linear factor descends with the exact
original coefficient realization and scalar normalization. -/
theorem normalized_repeated_linear_factor_constructs_full_factorization {n : ℕ}
    (f : K →+* E) (P : MvPolynomial (Fin n) K) (d : ℕ)
    (a b : Fin n → E) (j : Fin n) (hbj : b j ≠ 0)
    (B : Fin n → K) (hBj : B j = 1) (hB : ∀ i, f (B i) = b i / b j)
    (hP : MvPolynomial.map f P = linearFormPolynomial a * linearFormPolynomial b ^ d) :
    ∃ A : Fin n → K, (∀ i, f (A i) = b j ^ d * a i) ∧
      P = linearFormPolynomial A * linearFormPolynomial B ^ d := by
  have hbcoeff : b = fun i => b j * f (B i) := by
    funext i
    rw [hB]
    field_simp [hbj]
  have hLb : coefficientLinearForm b = C (b j) * coefficientLinearForm (fun i => f (B i)) := by
    calc
      _ = coefficientLinearForm (fun i => b j * f (B i)) := congrArg coefficientLinearForm hbcoeff
      _ = _ := coefficientLinearForm_mul_coefficients (b j) (fun i => f (B i))
  let a' : Fin n → E := fun i => b j ^ d * a i
  have ha' : coefficientLinearForm a' = C (b j ^ d) * coefficientLinearForm a :=
    coefficientLinearForm_mul_coefficients _ _
  have hP' : MvPolynomial.map f P = coefficientLinearForm (fun i => f (B i)) ^ d * coefficientLinearForm a' := by
    calc
      _ = coefficientLinearForm a * (C (b j) * coefficientLinearForm (fun i => f (B i))) ^ d := by
        rw [← hLb]
        exact hP
      _ = _ := by rw [ha', mul_pow, map_pow]; ring
  obtain ⟨A, hA, hfactor⟩ := normalized_linear_power_quotient_descends f f.injective P B j hBj d a' hP'
  refine ⟨A, hA, ?_⟩
  exact hfactor.trans (mul_comm _ _)

variable [CharZero E]

/-- The actual binary Hessian recovers the normalized repeated factor
over the original field when the two ruling forms are independent. -/
theorem binary_independent_linear_power_repeated_covector_descends
    (f : K →+* E) (P : MvPolynomial (Fin 2) K) (a b : Fin 2 → E)
    (d : ℕ) (hd : 1 < d) (hdet : a 0 * b 1 - a 1 * b 0 ≠ 0)
    (j : Fin 2) (hbj : b j ≠ 0)
    (hP : MvPolynomial.map f P = linearFormPolynomial a * linearFormPolynomial b ^ d) :
    ∃ B : Fin 2 → K, B j = 1 ∧ ∀ i, f (B i) = b i / b j := by
  have hdE : (d : E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs : -((d : E) ^ 2) * (a 0 * b 1 - a 1 * b 0) ^ 2 ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hdE)) (pow_ne_zero 2 hdet)
  have hH : MvPolynomial.map f (binaryHessianDeterminant P) =
      C (-((d : E) ^ 2) * (a 0 * b 1 - a 1 * b 0) ^ 2) * linearFormPolynomial b ^ (2 * d - 2) := by
    rw [binaryHessianDeterminant_map, hP, binary_linear_power_hessian_identity]
  obtain ⟨B, hBj, hB, _hvalue⟩ := linear_power_normalized_covector_descends f (binaryHessianDeterminant P)
    (by omega : 0 < 2 * d - 2) b _ hs j hbj hH
  exact ⟨B, hBj, hB⟩

/-- A nonzero original binary form which becomes linear-times-dth-power
under any field embedding has that full factorization over its original
field when d>1. Both original covectors, their exact normalization and
the proportional-factor case are retained. No descent hypothesis is supplied. -/
theorem binary_linear_times_power_factorization_descends
    (f : K →+* E) (P : MvPolynomial (Fin 2) K) (hP0 : P ≠ 0)
    (a b : Fin 2 → E) (d : ℕ) (hd : 1 < d)
    (hP : MvPolynomial.map f P = linearFormPolynomial a * linearFormPolynomial b ^ d) :
    ∃ (j : Fin 2) (B A : Fin 2 → K), b j ≠ 0 ∧ B j = 1 ∧
      (∀ i, f (B i) = b i / b j) ∧ (∀ i, f (A i) = b j ^ d * a i) ∧
      P = linearFormPolynomial A * linearFormPolynomial B ^ d := by
  have hmap : MvPolynomial.map f P ≠ 0 := by
    intro hz
    exact hP0 ((MvPolynomial.map_injective f f.injective) (hz.trans (map_zero _).symm))
  have ha : a ≠ 0 := by
    intro hz
    apply hmap
    rw [hP, hz]
    simp [linearFormPolynomial]
  have hb : b ≠ 0 := by
    intro hz
    apply hmap
    rw [hP, hz]
    simp [linearFormPolynomial, show d ≠ 0 from by omega]
  obtain ⟨j, hbj⟩ : ∃ j, b j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hb
  have hnormalized : ∃ B : Fin 2 → K, B j = 1 ∧ ∀ i, f (B i) = b i / b j := by
    by_cases hdet : a 0 * b 1 - a 1 * b 0 = 0
    · have hcross (i k : Fin 2) : b i * a k - b k * a i = 0 := by
        fin_cases i <;> fin_cases k
        · ring
        · change b 0 * a 1 - b 1 * a 0 = 0
          linear_combination -hdet
        · change b 1 * a 0 - b 0 * a 1 = 0
          linear_combination hdet
        · ring
      obtain ⟨α, hα, hαb⟩ := nonzero_vectors_proportional_of_cross_equations b a hb ha hcross
      have hpure : MvPolynomial.map f P = C α * linearFormPolynomial b ^ (d + 1) := by
        rw [hP, funext hαb]
        change coefficientLinearForm (fun i => α * b i) * coefficientLinearForm b ^ d =
          C α * coefficientLinearForm b ^ (d + 1)
        rw [coefficientLinearForm_mul_coefficients, pow_succ]
        ring
      obtain ⟨B, hBj, hB, _hvalue⟩ := linear_power_normalized_covector_descends f P
        (Nat.succ_pos d) b α hα j hbj hpure
      exact ⟨B, hBj, hB⟩
    · exact binary_independent_linear_power_repeated_covector_descends f P a b d hd hdet j hbj hP
  obtain ⟨B, hBj, hB⟩ := hnormalized
  obtain ⟨A, hA, hfactor⟩ := normalized_repeated_linear_factor_constructs_full_factorization
    f P d a b j hbj B hBj hB hP
  exact ⟨j, B, A, hbj, hBj, hB, hA, hfactor⟩

end DimensionFourDependence
