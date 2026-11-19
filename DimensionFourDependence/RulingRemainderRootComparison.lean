import DimensionFourDependence.LinearPowerRemainderRootUniqueness
import DimensionFourDependence.RationalRulingPolynomialIdentity
import DimensionFourDependence.UnivariateLinearPowerDescent

/-! # Equal actual generic ruling values retain the same selected remainder root -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3000000

variable {K E F : Type u} [Field K] [CharZero K] [Field E] [Algebra K E] [Field F]

/-- A derivative-one ruling coordinate compares two actual
linear-times-power values as complete homogeneous binary forms.
Consequently their remainder roots agree in any specified field
realization, including the selected original projective coordinate field. -/
theorem ruling_factored_generic_value_preserves_remainder_root
    (D : Derivation K E E) (s : E) (hs : D s = 1)
    (a b c e : Fin 2 → E) (d : ℕ) (hd : 1 < d)
    (ha : ∀ i, D (a i) = 0) (hb : ∀ i, D (b i) = 0)
    (hc : ∀ i, D (c i) = 0) (he : ∀ i, D (e i) = 0)
    (hvalue : (segreRulingPowerPolynomial a b d).eval s =
      (segreRulingPowerPolynomial c e d).eval s)
    (hvalue0 : (segreRulingPowerPolynomial a b d).eval s ≠ 0)
    (φ : E →+* F) (w : Fin 2 → F)
    (hroot : φ (a 0) * w 0 + φ (a 1) * w 1 = 0) :
    φ (c 0) * w 0 + φ (c 1) * w 1 = 0 := by
  have hp : segreRulingPowerPolynomial a b d = segreRulingPowerPolynomial c e d := by
    apply sub_eq_zero.mp
    apply polynomial_constant_coefficients_eval_zero_implies_zero D s hs
    · intro i
      rw [Polynomial.coeff_sub, map_sub,
        ruling_power_polynomial_constant_coefficients D a b ha hb d i,
        ruling_power_polynomial_constant_coefficients D c e hc he d i, sub_self]
    · rw [Polynomial.eval_sub]
      exact sub_eq_zero.mpr hvalue
  have hnonzero (v z : Fin 2 → E)
      (h : (segreRulingPowerPolynomial v z d).eval s ≠ 0) : v ≠ 0 ∧ z ≠ 0 := by
    constructor
    · intro hv
      apply h
      simp [segreRulingPowerPolynomial, segreRulingAffineFactor, hv]
    · intro hz
      apply h
      simp [segreRulingPowerPolynomial, segreRulingAffineFactor, hz, show d ≠ 0 from by omega]
  have hab := hnonzero a b hvalue0
  have hce := hnonzero c e (by rw [← hp]; exact hvalue0)
  have hflip (v : Fin 2 → E) (hv : v ≠ 0) : (![v 1, v 0] : Fin 2 → E) ≠ 0 := by
    intro hz
    have h0 := congrFun hz 1
    have h1 := congrFun hz 0
    change v 0 = 0 at h0
    change v 1 = 0 at h1
    apply hv
    funext i
    fin_cases i
    · exact h0
    · exact h1
  have hbin := congrArg (fun P : Polynomial E => P.homogenize (d + 1)) hp
  simp only [segre_ruling_power_polynomial_homogenize] at hbin
  have heval (v : Fin 2 → E) :
      MvPolynomial.eval₂ φ ![w 1, w 0] (linearFormPolynomial ![v 1, v 0]) =
        φ (v 0) * w 0 + φ (v 1) * w 1 := by
    simp [linearFormPolynomial, Fin.sum_univ_two]
    ring
  have hroot' : MvPolynomial.eval₂ φ ![w 1, w 0] (linearFormPolynomial ![a 1, a 0]) = 0 := by
    rw [heval]
    exact hroot
  have hresult := linear_times_power_remainder_root_preserved φ
    ![a 1, a 0] ![b 1, b 0] ![c 1, c 0] ![e 1, e 0]
    (hflip a hab.1) (hflip b hab.2) (hflip c hce.1) (hflip e hce.2)
    d hd hbin ![w 1, w 0] hroot'
  rwa [heval] at hresult

end DimensionFourDependence
