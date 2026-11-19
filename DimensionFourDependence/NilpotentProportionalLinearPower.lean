import DimensionFourDependence.SegreGlobalLinearRoot
import DimensionFourDependence.LinearPowerRemainderRootUniqueness

/-! # The final nonzero radial-pairing eigenvalue contradiction in the original source ring -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- A nonzero source linear form cannot have its dth power equal to
the output combination with a proportional nonzero constant covector
when the original Jacobian is nilpotent. Differentiation constructs the
actual nonzero polynomial left eigenvalue and nilpotence excludes it. -/
theorem nilpotent_proportional_linear_power_identity_impossible
    (H : Fin n → MvPolynomial (Fin n) K) (hN : IsNilpotent (jac H))
    (d : ℕ) (hd : 0 < d) (a l : Fin n → K) (hl : l ≠ 0)
    (α : K) (hα : α ≠ 0) (hprop : ∀ i, l i = α * a i)
    (hpower : linearFormPolynomial l ^ d = outputLinearCombination H a) : False := by
  have hscale : outputLinearCombination H l = C α * outputLinearCombination H a := by
    simp only [outputLinearCombination, hprop, map_mul, Finset.mul_sum, mul_assoc]
  have hpowerL : outputLinearCombination H l = C α * linearFormPolynomial l ^ d := by
    rw [hscale, hpower]
  let v : Fin n → MvPolynomial (Fin n) K := fun i => C (l i)
  let ev : MvPolynomial (Fin n) K := C α * (d : MvPolynomial (Fin n) K) * linearFormPolynomial l ^ (d - 1)
  have hv : v ≠ 0 := by
    intro hz
    apply hl
    funext i
    apply MvPolynomial.C_injective (Fin n) K
    simpa only [v, Pi.zero_apply, map_zero] using congrFun hz i
  have hderiv (j : Fin n) := congrArg (pderiv j) hpowerL
  have heigen : v ᵥ* jac H = ev • v := by
    funext j
    change (∑ i, C (l i) * pderiv j (H i)) = ev * C (l j)
    simpa only [outputLinearCombination, map_sum, pderiv_C_mul, pderiv_pow,
      linearFormPolynomial_pderiv, nsmul_eq_mul, smul_eq_mul, ev, mul_assoc] using hderiv j
  have heigenzero := eigenvalue_zero_of_nilpotent (jac H) hN v hv ev heigen
  have hL : linearFormPolynomial l ≠ 0 := coefficientLinearForm_ne_zero l hl
  have heigennonzero : ev ≠ 0 := mul_ne_zero
    (mul_ne_zero (MvPolynomial.C_ne_zero.mpr hα) (Nat.cast_ne_zero.mpr (by omega)))
    (pow_ne_zero (d - 1) hL)
  exact heigennonzero heigenzero

end DimensionFourDependence
