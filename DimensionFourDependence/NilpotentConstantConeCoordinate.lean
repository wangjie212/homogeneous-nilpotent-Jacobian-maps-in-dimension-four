import DimensionFourDependence.SecondCoordinateAffineChart

/-! # Nilpotence excludes a constant second cone scalar

A pure coordinate power gives an actual polynomial left eigenvector of
the original Jacobian. Nilpotence makes its eigenvalue zero. Homogeneous
chart reconstruction applies this to a constant second chart coordinate,
so component independence forces its parameter polynomial derivative
nonzero before the final quadratic trace comparison.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- A homogeneous pure coordinate power in its own output position
has zero scalar coefficient when the actual Jacobian is nilpotent. -/
theorem nilpotent_pure_coordinate_power_scalar_zero
    (H : Fin n → MvPolynomial (Fin n) K) (hN : IsNilpotent (jac H))
    {d : ℕ} (hd : 0 < d) (j : Fin n) (c : K)
    (hpower : H j = C c * X j ^ d) : c = 0 := by
  classical
  let a : MvPolynomial (Fin n) K := C c * (d : MvPolynomial (Fin n) K) * X j ^ (d - 1)
  have hv : (Pi.single j 1 : Fin n → MvPolynomial (Fin n) K) ≠ 0 := by
    intro hz
    have he := congrFun hz j
    simp only [Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at he
  have he : (Pi.single j 1 : Fin n → MvPolynomial (Fin n) K) ᵥ* jac H =
      a • (Pi.single j 1) := by
    rw [Matrix.single_one_vecMul]
    funext k
    change pderiv k (H j) = a * (Pi.single j 1 : Fin n → MvPolynomial (Fin n) K) k
    rw [hpower, pderiv_C_mul, pderiv_pow, pderiv_X]
    by_cases hk : k = j <;> simp [Pi.single_apply, hk, eq_comm, a] <;> ring
  have ha : a = 0 := eigenvalue_zero_of_nilpotent (jac H) hN (Pi.single j 1) hv a he
  have hcd : C c * (d : MvPolynomial (Fin n) K) = 0 :=
    (mul_eq_zero.mp ha).resolve_right (pow_ne_zero (d - 1) (X_ne_zero j))
  have hc : C c = (0 : MvPolynomial (Fin n) K) :=
    (mul_eq_zero.mp hcd).resolve_right (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
  apply MvPolynomial.C_injective (Fin n) K
  simpa only [map_zero] using hc

omit [CharZero K] in
/-- A constant original affine chart coordinate reconstructs exactly
as its scalar times the original homogeneous y power. -/
theorem constant_second_chart_coordinate_reconstructs_homogeneous_power
    (F : MvPolynomial (Fin 4) K) {d : ℕ} (hF : F.IsHomogeneous d) (c : K)
    (hchart : secondCoordinateAffineChart F = C c) :
    F = C c * X (1 : Fin 4) ^ d := by
  apply secondCoordinateAffineChart_injective_homogeneous F _ hF
  · simpa only [Nat.one_mul, Nat.mul_one] using
      ((isHomogeneous_X (R := K) (1 : Fin 4)).pow d).C_mul c
  · rw [hchart]
    simp [secondCoordinateAffineChart_eq_aeval]

/-- A constant second affine coordinate of the original homogeneous
nilpotent map is zero and forces a constant component relation. -/
theorem nilpotent_constant_second_chart_coordinate_forces_dependence
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hN : IsNilpotent (jac H)) (c : K)
    (hchart : secondCoordinateAffineChart (H 1) = C c) :
    H 1 = 0 ∧ ComponentsDependent H := by
  classical
  have hp := constant_second_chart_coordinate_reconstructs_homogeneous_power (H 1) (hH 1) c hchart
  have hc := nilpotent_pure_coordinate_power_scalar_zero H hN hd 1 c hp
  have hz : H 1 = 0 := by rw [hp, hc, map_zero, zero_mul]
  refine ⟨hz, Pi.single (1 : Fin 4) (1 : K), ?_, ?_⟩
  · intro he
    have h := congrFun he 1
    simp only [Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at h
  · simp [Pi.single_apply, hz]

/-- In the actual independent nilpotent map, the second affine scalar
polynomial cannot have zero derivative. The final quadratic trace
comparison must therefore give a contradiction. -/
theorem independent_nilpotent_second_affine_scalar_derivative_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hN : IsNilpotent (jac H)) (hind : ¬ ComponentsDependent H)
    (P : MvPolynomial (Fin 3) K) (A : Polynomial K)
    (hchart : secondCoordinateAffineChart (H 1) = Polynomial.aeval P A) :
    A.derivative ≠ 0 := by
  intro hz
  have hA := Polynomial.eq_C_of_derivative_eq_zero hz
  have hc : secondCoordinateAffineChart (H 1) = C (A.coeff 0) := by
    rw [hchart]
    conv_lhs => rw [hA]
    rw [Polynomial.aeval_C]
    rfl
  exact hind (nilpotent_constant_second_chart_coordinate_forces_dependence H hd hH hN (A.coeff 0) hc).2

end DimensionFourDependence
