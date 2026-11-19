import DimensionFourDependence.HomogenizedTernaryNormalForm
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # The unique quadratic relation of the canonical ternary perturbation -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3900000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "W" => Polynomial (Polynomial K)

/-- Evaluate a linear-minus-quadratic relation on an actual triple. -/
noncomputable def ternaryQuadraticRelation (l : Fin 3 → K) (Q : Matrix (Fin 3) (Fin 3) K)
    (H : Fin 3 → R₃) : R₃ :=
  (∑ i, C (l i) * H i) - ∑ i, ∑ j, C (Q i j) * H i * H j

omit [CharZero K] in
private theorem polynomial_eq_zero_of_comp_positive_degree
    (P Q : Polynomial K) (hP : 0 < P.natDegree) (h : Q.comp P = 0) : Q = 0 := by
  rcases Polynomial.comp_eq_zero_iff.mp h with hQ | ⟨_, he⟩
  · exact hQ
  · have hz := congrArg Polynomial.natDegree he
    rw [Polynomial.natDegree_C] at hz
    omega

/-- The sole relation of degree at most two of a normalized canonical
perturbation is its scalar multiple of `H₂ - H₀²`. This is stated
coefficientwise for a symmetric quadratic form. -/
theorem ternary_normal_form_symmetric_quadratic_relation_unique
    (P : Polynomial K) (hP : 0 < P.natDegree)
    (l : Fin 3 → K) (Q : Matrix (Fin 3) (Fin 3) K) (hQ : Q.transpose = Q)
    (h : ternaryQuadraticRelation l Q (TernaryNormalForm.perturbation3 P) = 0) :
    (∀ i, l i = if i = 2 then l 2 else 0) ∧
      ∀ i j, Q i j = if i = 0 ∧ j = 0 then l 2 else 0 := by
  let z : Fin 3 → W := ![0, Polynomial.C Polynomial.X, Polynomial.X]
  let e : R₃ →ₐ[K] W := aeval z
  let A : Polynomial K := Polynomial.C (l 0) * P + Polynomial.C (l 2 - Q 0 0) * P ^ 2 -
    Polynomial.C (2 * Q 0 2) * P ^ 3 - Polynomial.C (Q 2 2) * P ^ 4
  let B : Polynomial K := Polynomial.C (l 1) - Polynomial.C (2 * Q 0 1) * P - Polynomial.C (2 * Q 1 2) * P ^ 2
  have hs (i j : Fin 3) : Q i j = Q j i := (congrFun (congrFun hQ j) i)
  let U := Polynomial.aeval (X 1 + (X 0 : R₃) ^ 2) P
  have heU : e U = Polynomial.C P := by
    change e (Polynomial.aeval (X 1 + (X 0 : R₃) ^ 2) P) = _
    rw [← Polynomial.aeval_algHom_apply, map_add, map_pow, aeval_X, aeval_X]
    have hz : z 1 + z 0 ^ 2 = Polynomial.C Polynomial.X := by
      change Polynomial.C Polynomial.X + (0 : W) ^ 2 = _
      simp
    rw [hz]
    let j : Polynomial K →ₐ[K] W := IsScalarTower.toAlgHom K (Polynomial K) W
    change Polynomial.aeval (j Polynomial.X) P = j P
    rw [Polynomial.aeval_algHom_apply j, Polynomial.aeval_X_left_apply]
  have hx : e (X (0 : Fin 3)) = 0 := aeval_X _ _
  have hz : e (X (2 : Fin 3)) = Polynomial.X := aeval_X _ _
  have hOut : (fun i => e (TernaryNormalForm.perturbation3 P i)) =
      (![Polynomial.C P, Polynomial.X, Polynomial.C (P ^ 2)] : Fin 3 → W) := by
    funext i
    fin_cases i
    · exact heU
    · change e (X 2 - 2 * X 0 * U) = Polynomial.X
      rw [map_sub, map_mul, map_mul, hz, hx, mul_zero, zero_mul, sub_zero]
    · change e (U ^ 2) = Polynomial.C (P ^ 2)
      rw [map_pow, heU, map_pow]
  have he (a : K) : e (C a) = Polynomial.C (Polynomial.C a) := e.commutes a
  have hTwo : Polynomial.C A + Polynomial.C B * Polynomial.X -
      Polynomial.C (Polynomial.C (Q 1 1)) * Polynomial.X ^ 2 = (0 : W) := by
    have heq := congrArg e h
    change e (ternaryQuadraticRelation l Q (TernaryNormalForm.perturbation3 P)) = e 0 at heq
    simp only [ternaryQuadraticRelation, map_sub, map_sum, map_mul, map_zero, he] at heq
    have hOut' (i : Fin 3) : e (TernaryNormalForm.perturbation3 P i) =
        (![Polynomial.C P, Polynomial.X, Polynomial.C (P ^ 2)] : Fin 3 → W) i := congrFun hOut i
    simp only [hOut', Fin.sum_univ_three] at heq
    have he' : Polynomial.C (Polynomial.C (l 0)) * Polynomial.C P +
        Polynomial.C (Polynomial.C (l 1)) * Polynomial.X + Polynomial.C (Polynomial.C (l 2)) * Polynomial.C (P ^ 2) -
        ((Polynomial.C (Polynomial.C (Q 0 0)) * Polynomial.C P * Polynomial.C P +
          Polynomial.C (Polynomial.C (Q 0 1)) * Polynomial.C P * Polynomial.X +
          Polynomial.C (Polynomial.C (Q 0 2)) * Polynomial.C P * Polynomial.C (P ^ 2)) +
         (Polynomial.C (Polynomial.C (Q 1 0)) * Polynomial.X * Polynomial.C P +
          Polynomial.C (Polynomial.C (Q 1 1)) * Polynomial.X * Polynomial.X +
          Polynomial.C (Polynomial.C (Q 1 2)) * Polynomial.X * Polynomial.C (P ^ 2)) +
         (Polynomial.C (Polynomial.C (Q 2 0)) * Polynomial.C (P ^ 2) * Polynomial.C P +
          Polynomial.C (Polynomial.C (Q 2 1)) * Polynomial.C (P ^ 2) * Polynomial.X +
          Polynomial.C (Polynomial.C (Q 2 2)) * Polynomial.C (P ^ 2) * Polynomial.C (P ^ 2))) = 0 := heq
    rw [hs 1 0, hs 2 0, hs 2 1] at he'
    simp only [map_pow] at he'
    simp only [A, B, map_mul, map_add, map_sub, map_pow, map_ofNat]
    linear_combination he'
  have h₁' (p : Polynomial K) (n : ℕ) : (Polynomial.C p * Polynomial.X : W).coeff n = if n = 1 then p else 0 := by
    rw [← pow_one (Polynomial.X : W), Polynomial.coeff_C_mul_X_pow]
  have hA : A = 0 := by
    have he := congrArg (fun p : W => p.coeff 0) hTwo
    change (Polynomial.C A + Polynomial.C B * Polynomial.X -
      Polynomial.C (Polynomial.C (Q 1 1)) * Polynomial.X ^ 2 : W).coeff 0 = (0 : W).coeff 0 at he
    rw [Polynomial.coeff_sub, Polynomial.coeff_add] at he
    simpa [h₁', Polynomial.coeff_C_mul_X_pow] using he
  have hB : B = 0 := by
    have he := congrArg (fun p : W => p.coeff 1) hTwo
    change (Polynomial.C A + Polynomial.C B * Polynomial.X -
      Polynomial.C (Polynomial.C (Q 1 1)) * Polynomial.X ^ 2 : W).coeff 1 = (0 : W).coeff 1 at he
    rw [Polynomial.coeff_sub, Polynomial.coeff_add] at he
    simpa [h₁', Polynomial.coeff_C_mul_X_pow] using he
  have h11 : Q 1 1 = 0 := by
    have he := congrArg (fun p : W => p.coeff 2) hTwo
    change (Polynomial.C A + Polynomial.C B * Polynomial.X -
      Polynomial.C (Polynomial.C (Q 1 1)) * Polynomial.X ^ 2 : W).coeff 2 = (0 : W).coeff 2 at he
    rw [Polynomial.coeff_sub, Polynomial.coeff_add] at he
    simpa [h₁', Polynomial.coeff_C_mul_X_pow] using he
  let A₀ : Polynomial K := Polynomial.C (l 0) * Polynomial.X + Polynomial.C (l 2 - Q 0 0) * Polynomial.X ^ 2 -
    Polynomial.C (2 * Q 0 2) * Polynomial.X ^ 3 - Polynomial.C (Q 2 2) * Polynomial.X ^ 4
  let B₀ : Polynomial K := Polynomial.C (l 1) - Polynomial.C (2 * Q 0 1) * Polynomial.X -
    Polynomial.C (2 * Q 1 2) * Polynomial.X ^ 2
  have hA₀ : A₀ = 0 := polynomial_eq_zero_of_comp_positive_degree P A₀ hP (by
    simpa only [A₀, A, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp,
      Polynomial.X_comp] using hA)
  have hB₀ : B₀ = 0 := polynomial_eq_zero_of_comp_positive_degree P B₀ hP (by
    simpa only [B₀, B, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp,
      Polynomial.X_comp] using hB)
  have hAcoeff (n : ℕ) := congrArg (fun p : Polynomial K => p.coeff n) hA₀
  have hBcoeff (n : ℕ) := congrArg (fun p : Polynomial K => p.coeff n) hB₀
  have hc (a : K) (n : ℕ) : (Polynomial.C a * Polynomial.X).coeff n = if n = 1 then a else 0 := by
    rw [← pow_one (Polynomial.X : Polynomial K), Polynomial.coeff_C_mul_X_pow]
  simp only [A₀, Polynomial.coeff_sub, Polynomial.coeff_add, hc, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hAcoeff
  simp only [B₀, Polynomial.coeff_sub, Polynomial.coeff_C, hc, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hBcoeff
  have hl0 : l 0 = 0 := by simpa using hAcoeff 1
  have hl1 : l 1 = 0 := by simpa using hBcoeff 0
  have h00 : Q 0 0 = l 2 := (sub_eq_zero.mp (by simpa using hAcoeff 2)).symm
  have hw (a : K) (he : 2 * a = 0) : a = 0 := (mul_eq_zero.mp he).resolve_left two_ne_zero
  have h02 : Q 0 2 = 0 := hw _ (by simpa using hAcoeff 3)
  have h22 : Q 2 2 = 0 := by simpa using hAcoeff 4
  have h01 : Q 0 1 = 0 := hw _ (by simpa using hBcoeff 1)
  have h12 : Q 1 2 = 0 := hw _ (by simpa using hBcoeff 2)
  constructor
  · intro i
    fin_cases i <;> simp [hl0, hl1]
  · intro i j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact h00
      | exact h11
      | exact h22
      | exact h01
      | exact h02
      | exact h12
      | exact (hs 1 0).trans h01
      | exact (hs 2 0).trans h02
      | exact (hs 2 1).trans h12

end DimensionFourDependence
