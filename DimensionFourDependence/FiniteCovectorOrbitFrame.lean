import DimensionFourDependence.NormalizedPencilOrbitMinor

/-! # One actual normalized frame avoids a finite family of covector planes -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 3500000

variable {K : Type*} [Field K] {n : ℕ}

/-- Finitely many nonzero source polynomials are simultaneously
nonzero at an actual point over the original infinite field. -/
theorem finite_nonzero_source_polynomials_construct_simultaneous_nonzero_point
    [Infinite K] {ι : Type*} (S : Finset ι) (P : ι → MvPolynomial (Fin n) K)
    (hP : ∀ i ∈ S, P i ≠ 0) (W : MvPolynomial (Fin n) K) (hW : W ≠ 0) :
    ∃ x : Fin n → K, aeval x W ≠ 0 ∧ ∀ i ∈ S, aeval x (P i) ≠ 0 := by
  classical
  have hprod : (∏ i ∈ S, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hP
  obtain ⟨x, hx⟩ := polynomial_exists_source_value_ne_zero _ (mul_ne_zero hW hprod)
  have hx' : aeval x W * ∏ i ∈ S, aeval x (P i) ≠ 0 := by
    simpa only [aeval_eq_eval, map_mul, map_prod] using hx
  exact ⟨x, (mul_ne_zero_iff.mp hx').1,
    Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hx').2⟩

/-- Euler's polynomial identity gives the literal first two
Jacobian orbit columns at every original-field source point. -/
theorem homogeneous_jacobian_point_orbit_output_acceleration
    (H : Fin n → MvPolynomial (Fin n) K) {d : ℕ} (hH : IsHomogMap H d)
    (x : Fin n → K) :
    (jac H).map (aeval x) *ᵥ x = (d : K) • (fun i => aeval x (H i)) ∧
      ((jac H).map (aeval x)) ^ 2 *ᵥ x =
        (d : K) • (fun i => aeval x ((jac H *ᵥ H) i)) := by
  have he := congrArg (fun v : Fin n → MvPolynomial (Fin n) K => fun i => aeval x (v i))
    (euler_identity H hH)
  have hfirst : (jac H).map (aeval x) *ᵥ x = (d : K) • (fun i => aeval x (H i)) := by
    funext i
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, coordVec,
      aeval_X, Pi.smul_apply, map_nsmul, nsmul_eq_mul, smul_eq_mul, map_natCast] using congrFun he i
  refine ⟨hfirst, ?_⟩
  rw [pow_two, ← Matrix.mulVec_mulVec, hfirst]
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
    map_sum, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

variable [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- A finite family of nonzero actual covector minors admits one
original-field point where all minors are nonzero and the nilpotent
Jacobian still has a nonzero second orbit. -/
theorem finite_nonzero_covector_orbit_minors_construct_actual_source_point
    (H : Fin 4 → R₀) (hW : jac H ^ 2 *ᵥ coordVec ≠ 0)
    (F : Finset ((Fin 4 → K) × (Fin 4 → K)))
    (hF : ∀ c ∈ F,
      outputLinearCombination H c.1 * outputLinearCombination (jac H *ᵥ H) c.2 -
        outputLinearCombination H c.2 * outputLinearCombination (jac H *ᵥ H) c.1 ≠ 0) :
    ∃ x : Fin 4 → K, ((jac H).map (aeval x)) ^ 2 *ᵥ x ≠ 0 ∧
      ∀ c ∈ F, aeval x
        (outputLinearCombination H c.1 * outputLinearCombination (jac H *ᵥ H) c.2 -
          outputLinearCombination H c.2 * outputLinearCombination (jac H *ᵥ H) c.1) ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, (jac H ^ 2 *ᵥ coordVec) i ≠ 0 := by
    simpa only [ne_eq, _root_.funext_iff, Pi.zero_apply, not_forall] using hW
  obtain ⟨x, hx, hminors⟩ :=
    finite_nonzero_source_polynomials_construct_simultaneous_nonzero_point F _ hF _ hi
  refine ⟨x, ?_, hminors⟩
  intro hz
  have he := congrFun ((polynomial_jacobian_second_euler_iterate_point_value H x).trans hz) i
  exact hx (by simpa only [Pi.zero_apply] using he)

/-- Every finite collection of constant covector pairs with nonzero
actual source minors admits a single normalized coordinate frame in
which every pair has nonzero determinant on columns one and two.
The source point and inverse coordinate matrices are constructed. -/
theorem finite_nonzero_covector_orbit_minors_construct_normalized_avoiding_frame
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hW : jac H ^ 2 *ᵥ coordVec ≠ 0)
    (F : Finset ((Fin 4 → K) × (Fin 4 → K)))
    (hF : ∀ c ∈ F,
      outputLinearCombination H c.1 * outputLinearCombination (jac H *ᵥ H) c.2 -
        outputLinearCombination H c.2 * outputLinearCombination (jac H *ᵥ H) c.1 ≠ 0) :
    ∃ T S : Matrix (Fin 4) (Fin 4) K, T * S = 1 ∧ S * T = 1 ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K))
        (pderiv 0 (linearPolynomialConjugate T S H i)) = if i = 1 then 1 else 0) ∧
      (∀ i, aeval (Pi.single (0 : Fin 4) (1 : K))
        (pderiv 1 (linearPolynomialConjugate T S H i)) = if i = 2 then 1 else 0) ∧
      ∀ c ∈ F,
        (∑ i, c.1 i * T i 1) * (∑ i, c.2 i * T i 2) -
          (∑ i, c.2 i * T i 1) * (∑ i, c.1 i * T i 2) ≠ 0 := by
  obtain ⟨x, hx, hminors⟩ :=
    finite_nonzero_covector_orbit_minors_construct_actual_source_point H hW F hF
  obtain ⟨T, S, hTS, hST, _hcol0, hcol1, hcol2, hj0, hj1⟩ :=
    nilpotent_jacobian_point_constructs_normalized_three_column_coordinates H hN x hx
  obtain ⟨he1, he2⟩ := homogeneous_jacobian_point_orbit_output_acceleration H hH x
  have hpair1 (μ : Fin 4 → K) : (∑ i, μ i * T i 1) = (d : K) * aeval x (outputLinearCombination H μ) := by
    simp only [hcol1, he1, Pi.smul_apply, smul_eq_mul, outputLinearCombination,
      map_sum, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hpair2 (μ : Fin 4 → K) :
      (∑ i, μ i * T i 2) = (d : K) * aeval x (outputLinearCombination (jac H *ᵥ H) μ) := by
    simp only [hcol2, he2, Pi.smul_apply, smul_eq_mul, outputLinearCombination,
      map_sum, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨T, S, hTS, hST, hj0, hj1, ?_⟩
  intro c hc
  have hdet :
      (∑ i, c.1 i * T i 1) * (∑ i, c.2 i * T i 2) -
        (∑ i, c.2 i * T i 1) * (∑ i, c.1 i * T i 2) =
      (d : K) ^ 2 * aeval x
        (outputLinearCombination H c.1 * outputLinearCombination (jac H *ᵥ H) c.2 -
          outputLinearCombination H c.2 * outputLinearCombination (jac H *ᵥ H) c.1) := by
    rw [hpair1, hpair2, hpair1, hpair2]
    simp only [map_sub, map_mul]
    ring
  rw [hdet]
  exact mul_ne_zero (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hd.ne')) (hminors c hc)

end DimensionFourDependence
