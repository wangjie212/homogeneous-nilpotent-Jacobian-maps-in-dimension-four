import DimensionFourDependence.FiberPolynomialGradients

/-! # Recovering a pure linear power's covector over its coefficient field

For P=c L^d and a coordinate point e_j with L(e_j) nonzero, the ratios
of L's coefficients are (partial_i P)(e_j)/(d P(e_j)). A form over the
original coefficient field therefore constructs its normalized covector
there. This applies to arbitrary injective field realization, without
an algebraicity, Galois or supplied root-descent hypothesis.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000

variable {C E : Type*} [Field C] [Field E] {n : ℕ}

/-- Evaluating a linear form at a coordinate point recovers its
coefficient with that same original coordinate label. -/
theorem linearFormPolynomial_eval_coordinate_point (a : Fin n → E) (j : Fin n) :
    MvPolynomial.eval (Pi.single j 1) (linearFormPolynomial a) = a j := by
  classical
  simp [linearFormPolynomial, Pi.single_apply]

/-- Coefficient realization commutes with evaluation at the original
coordinate point. -/
theorem coefficient_map_eval_coordinate_point (f : C →+* E)
    (P : MvPolynomial (Fin n) C) (j : Fin n) :
    MvPolynomial.eval (Pi.single j 1) (MvPolynomial.map f P) =
      f (MvPolynomial.eval (Pi.single j 1) P) := by
  classical
  have hs : f ∘ (Pi.single j (1 : C)) = Pi.single j (1 : E) := by
    funext i
    simp [Pi.single_apply]
  simpa only [hs] using (MvPolynomial.map_eval f (Pi.single j 1) P).symm

/-- The gradient of a scalar linear power at a coordinate point has
its exact pure-power value, including the original positive degree. -/
theorem linear_power_gradient_coordinate_value (a : Fin n → E) (c : E) (d : ℕ)
    (i j : Fin n) :
    MvPolynomial.eval (Pi.single j 1) (pderiv i (MvPolynomial.C c * linearFormPolynomial a ^ d)) =
      c * ((d : E) * (a j) ^ (d - 1) * a i) := by
  rw [pderiv_C_mul, pderiv_pow, linearFormPolynomial_pderiv]
  simp only [map_mul, eval_C, map_natCast, map_pow, linearFormPolynomial_eval_coordinate_point]

/-- A normalized projective covector recovers every form in the same
pure-power family, including members whose scalar coefficient is zero. -/
theorem linear_power_form_of_normalized_covector
    (f : C →+* E) (P : MvPolynomial (Fin n) C) (d : ℕ)
    (a : Fin n → E) (c : E) (j : Fin n) (hj : a j ≠ 0)
    (b : Fin n → C) (hb : ∀ i, f (b i) = a i / a j)
    (hP : MvPolynomial.map f P = MvPolynomial.C c * linearFormPolynomial a ^ d) :
    P = MvPolynomial.C (MvPolynomial.eval (Pi.single j 1) P) * linearFormPolynomial b ^ d := by
  classical
  have hu : f (MvPolynomial.eval (Pi.single j 1) P) = c * a j ^ d := by
    rw [← coefficient_map_eval_coordinate_point, hP]
    simp only [map_mul, eval_C, map_pow, linearFormPolynomial_eval_coordinate_point]
  have hlin : linearFormPolynomial a = MvPolynomial.C (a j) * MvPolynomial.map f (linearFormPolynomial b) := by
    simp only [linearFormPolynomial, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, ← map_mul, hb i, mul_div_cancel₀ _ hj]
  apply MvPolynomial.map_injective f f.injective
  rw [map_mul, map_pow, MvPolynomial.map_C, hP, hlin, mul_pow, ← mul_assoc, ← map_pow, ← map_mul, hu]

variable [CharZero E]

/-- The coefficients of the normalized linear factor of a nonzero
pure-power form are recovered over its original coefficient field. -/
theorem linear_power_normalized_covector_descends
    (f : C →+* E) (P : MvPolynomial (Fin n) C) {d : ℕ} (hd : 0 < d)
    (a : Fin n → E) (c : E) (hc : c ≠ 0) (j : Fin n) (hj : a j ≠ 0)
    (hP : MvPolynomial.map f P = MvPolynomial.C c * linearFormPolynomial a ^ d) :
    ∃ b : Fin n → C, b j = 1 ∧ (∀ i, f (b i) = a i / a j) ∧
      MvPolynomial.eval (Pi.single j 1) P ≠ 0 := by
  classical
  let u : C := MvPolynomial.eval (Pi.single j 1) P
  have hu : f u = c * a j ^ d := by
    rw [← coefficient_map_eval_coordinate_point, hP]
    simp only [map_mul, eval_C, map_pow, linearFormPolynomial_eval_coordinate_point]
  have hu0 : u ≠ 0 := by
    intro hz
    have he := hu
    rw [hz, map_zero] at he
    exact (mul_ne_zero hc (pow_ne_zero d hj)) he.symm
  have hdegreeE : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  let b : Fin n → C := fun i =>
    MvPolynomial.eval (Pi.single j 1) (pderiv i P) / ((d : C) * u)
  have hb (i : Fin n) : f (b i) = a i / a j := by
    have hgradient : f (MvPolynomial.eval (Pi.single j 1) (pderiv i P)) =
        c * ((d : E) * (a j) ^ (d - 1) * a i) := by
      rw [← coefficient_map_eval_coordinate_point, ← pderiv_map, hP]
      exact linear_power_gradient_coordinate_value a c d i j
    simp only [b, map_div₀, map_mul, map_natCast, hgradient, hu]
    have hpow : (a j) ^ d = (a j) ^ (d - 1) * a j := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    rw [hpow]
    field_simp [hc, hj, hdegreeE]
  refine ⟨b, ?_, hb, hu0⟩
  apply f.injective
  rw [hb j, div_self hj, map_one]

/-- The reconstructed normalized factor recovers the entire original
form over the original field, not only its projective coefficient ratios. -/
theorem linear_power_factorization_descends
    (f : C →+* E) (P : MvPolynomial (Fin n) C) {d : ℕ} (hd : 0 < d)
    (a : Fin n → E) (c : E) (hc : c ≠ 0) (j : Fin n) (hj : a j ≠ 0)
    (hP : MvPolynomial.map f P = MvPolynomial.C c * linearFormPolynomial a ^ d) :
    ∃ b : Fin n → C, b j = 1 ∧ (∀ i, f (b i) = a i / a j) ∧
      MvPolynomial.eval (Pi.single j 1) P ≠ 0 ∧
      P = MvPolynomial.C (MvPolynomial.eval (Pi.single j 1) P) * linearFormPolynomial b ^ d := by
  classical
  obtain ⟨b, hbj, hb, hu0⟩ := linear_power_normalized_covector_descends f P hd a c hc j hj hP
  exact ⟨b, hbj, hb, hu0, linear_power_form_of_normalized_covector f P d a c j hj b hb hP⟩

/-- One nonzero member of a common linear-power family constructs the
same normalized covector and all scalar coefficients over the original
field. No algebraicity or Galois-action data are assumed. -/
theorem nonzero_linear_power_family_descends
    {m : ℕ} (f : C →+* E) (P : Fin m → MvPolynomial (Fin n) C)
    {d : ℕ} (hd : 0 < d) (a : Fin n → E) (c : Fin m → E)
    (k : Fin m) (hk : P k ≠ 0)
    (hP : ∀ i, MvPolynomial.map f (P i) = MvPolynomial.C (c i) * linearFormPolynomial a ^ d) :
    ∃ (j : Fin n) (b : Fin n → C), b j = 1 ∧ (∀ i, f (b i) = a i / a j) ∧
      ∃ u : Fin m → C, ∀ i,
        P i = MvPolynomial.C (u i) * linearFormPolynomial b ^ d ∧ f (u i) = c i * a j ^ d := by
  classical
  have hmap : MvPolynomial.map f (P k) ≠ 0 := by
    intro hz
    exact hk ((MvPolynomial.map_injective f f.injective) (hz.trans (map_zero _).symm))
  have hc : c k ≠ 0 := by intro hz; apply hmap; rw [hP k, hz, map_zero, zero_mul]
  have ha : a ≠ 0 := by
    intro hz
    apply hmap
    rw [hP k, hz]
    simp [linearFormPolynomial, Nat.ne_of_gt hd]
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using ha
  obtain ⟨b, hbj, hb, _hu⟩ := linear_power_normalized_covector_descends f (P k) hd a (c k) hc j hj (hP k)
  refine ⟨j, b, hbj, hb, fun i => MvPolynomial.eval (Pi.single j 1) (P i), ?_⟩
  intro i
  refine ⟨linear_power_form_of_normalized_covector f (P i) d a (c i) j hj b hb (hP i), ?_⟩
  rw [← coefficient_map_eval_coordinate_point, hP i]
  simp only [map_mul, eval_C, map_pow, linearFormPolynomial_eval_coordinate_point]

end DimensionFourDependence
