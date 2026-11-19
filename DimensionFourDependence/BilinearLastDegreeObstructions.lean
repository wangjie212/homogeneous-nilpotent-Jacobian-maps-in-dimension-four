import DimensionFourDependence.TernaryPolynomialLastVariable
import DimensionFourDependence.BilinearLeadingCoefficientObstruction

/-! # The bilinear trace equations cannot hold with moving last-variable outputs -/

namespace DimensionFourDependence

open MvPolynomial Polynomial

universe u
set_option maxHeartbeats 2200000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "P" => Polynomial R₂

omit [CharZero K] in
private theorem coeff_at_or_above_degree (U : P) {d : ℕ} (hd : U.natDegree ≤ d) :
    U.coeff d = 0 ∨ U.coeff d = U.leadingCoeff := by
  rcases lt_or_eq_of_le hd with h | h
  · exact Or.inl (coeff_eq_zero_of_natDegree_lt h)
  · exact Or.inr (by rw [← h]; rfl)

/-- If both independent outputs depend on the last variable, the
highest coefficient of the actual trace gives an impossible product
of two nonzero horizontal leading coefficients. -/
theorem bilinear_trace_both_last_degrees_positive_impossible
    (U V : P) (hU : 0 < U.natDegree) (hV : 0 < V.natDegree)
    (γ a b : K) (hγ : γ ≠ 0)
    (h : ternaryCoefficientPartial 0 U + ternaryCoefficientPartial 1 V +
        Polynomial.C (MvPolynomial.C γ) * (U * V).derivative +
        Polynomial.C (MvPolynomial.C a) * U.derivative +
        Polynomial.C (MvPolynomial.C b) * V.derivative = 0) : False := by
  let d := U.natDegree + V.natDegree - 1
  have hdU : U.natDegree ≤ d := by dsimp [d]; omega
  have hdV : V.natDegree ≤ d := by dsimp [d]; omega
  have hUder : U.derivative.coeff d = 0 := coeff_eq_zero_of_natDegree_lt
    ((natDegree_derivative_le U).trans_lt (by omega))
  have hVder : V.derivative.coeff d = 0 := coeff_eq_zero_of_natDegree_lt
    ((natDegree_derivative_le V).trans_lt (by omega))
  have hnext : d + 1 = U.natDegree + V.natDegree := by dsimp [d]; omega
  have hc := congrArg (fun Q : P => Q.coeff d) h
  change (ternaryCoefficientPartial 0 U + ternaryCoefficientPartial 1 V +
        Polynomial.C (MvPolynomial.C γ) * (U * V).derivative +
        Polynomial.C (MvPolynomial.C a) * U.derivative +
        Polynomial.C (MvPolynomial.C b) * V.derivative).coeff d = (0 : P).coeff d at hc
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_zero,
    ternaryCoefficientPartial_coeff, hUder, hVder, mul_zero, add_zero] at hc
  rw [Polynomial.coeff_derivative, hnext,
    Polynomial.coeff_mul_add_eq_of_natDegree_le (le_refl U.natDegree) (le_refl V.natDegree)] at hc
  let m := U.natDegree + V.natDegree
  have hcast : (d : R₂) + 1 = (m : R₂) := by
    simpa only [Nat.cast_add_one] using congrArg (fun i : ℕ => (i : R₂)) hnext
  rw [hcast] at hc
  have hm : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr (by dsimp [m]; omega)
  have hU0 : U ≠ 0 := by intro hz; rw [hz, natDegree_zero] at hU; omega
  have hV0 : V ≠ 0 := by intro hz; rw [hz, natDegree_zero] at hV; omega
  apply nonzero_leading_product_ne_negative_partial_sum U.leadingCoeff V.leadingCoeff
    (leadingCoeff_ne_zero.mpr hU0) (leadingCoeff_ne_zero.mpr hV0)
    (U.coeff d) (V.coeff d) (coeff_at_or_above_degree U hdU) (coeff_at_or_above_degree V hdV)
    0 1 (γ * (m : K)) (mul_ne_zero hγ hm)
  simp only [map_mul, map_natCast]
  change pderiv 0 (U.coeff d) + pderiv 1 (V.coeff d) +
    MvPolynomial.C γ * (U.leadingCoeff * V.leadingCoeff * (m : R₂)) = 0 at hc
  linear_combination hc

/-- The principal-minor equation when one output is fixed in the
last variable still produces the impossible leading square. -/
theorem bilinear_one_moving_last_degree_minor_impossible
    (V : P) (hV : 0 < V.natDegree) (u w : R₂) (hw : w ≠ 0) (i : Fin 2)
    (γ a : K) (hγ : γ ≠ 0)
    (h : Polynomial.C (u ^ 2) + Polynomial.C w *
      (ternaryCoefficientPartial i V + Polynomial.C (MvPolynomial.C γ) * (V * V.derivative) +
        Polynomial.C (MvPolynomial.C a) * V.derivative) = 0) : False := by
  let d := V.natDegree + (V.natDegree - 1)
  have hdV : V.natDegree ≤ d := by dsimp [d]; omega
  have hd : d ≠ 0 := by omega
  have hVder : V.derivative.coeff d = 0 := coeff_eq_zero_of_natDegree_lt
    ((natDegree_derivative_le V).trans_lt (by omega))
  have hD : V.derivative.natDegree = V.natDegree - 1 := natDegree_derivative V
  have hcoef : (V * V.derivative).coeff d = V.leadingCoeff * V.leadingCoeff * (V.natDegree : R₂) := by
    change (V * V.derivative).coeff (V.natDegree + (V.natDegree - 1)) = _
    rw [← hD, Polynomial.coeff_mul_add_eq_of_natDegree_le (le_refl V.natDegree)
      (le_refl V.derivative.natDegree)]
    change V.leadingCoeff * V.derivative.leadingCoeff = _
    rw [leadingCoeff_derivative, mul_assoc]
  have he := congrArg (fun Q : P => Q.coeff d) h
  change (Polynomial.C (u ^ 2) + Polynomial.C w *
      (ternaryCoefficientPartial i V + Polynomial.C (MvPolynomial.C γ) * (V * V.derivative) +
        Polynomial.C (MvPolynomial.C a) * V.derivative)).coeff d = (0 : P).coeff d at he
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_zero,
    ternaryCoefficientPartial_coeff, hd, ite_false, zero_add, hVder, mul_zero, add_zero, hcoef] at he
  have hm : (V.natDegree : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hV)
  have hV0 : V ≠ 0 := by intro hz; rw [hz, natDegree_zero] at hV; omega
  have hne := leadingCoeff_ne_zero.mpr hV0
  apply nonzero_leading_product_ne_negative_partial_sum V.leadingCoeff V.leadingCoeff hne hne
    (V.coeff d) 0 (coeff_at_or_above_degree V hdV) (Or.inl rfl)
    i i (γ * (V.natDegree : K)) (mul_ne_zero hγ hm)
  simp only [map_zero, add_zero, map_mul, map_natCast]
  have hs := (mul_eq_zero.mp he).resolve_left hw
  linear_combination hs

end DimensionFourDependence
