import DimensionFourDependence.BinaryLinearPowerDescent
import DimensionFourDependence.SegreRulingBinaryPolynomial
import DimensionFourDependence.ModifiedCubicFiberBoundary
import Mathlib.Algebra.Polynomial.Homogenize

/-! # Descent of the actual affine linear-times-power ruling presentation -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type*} [Field K] [Field E]

/-- Dehomogenization uses the original affine constant and varying coefficient. -/
theorem binary_linear_form_dehomogenize (a : Fin 2 → K) :
    MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial K)] (linearFormPolynomial a) =
      segreRulingAffineFactor ![a 1, a 0] := by
  simp [linearFormPolynomial, Fin.sum_univ_two, segreRulingAffineFactor]
  ring

/-- The actual affine ruling presentation homogenizes with no
assumption about its leading coefficient or the location of its zeros. -/
theorem segre_ruling_power_polynomial_homogenize (a b : Fin 2 → K) (d : ℕ) :
    (segreRulingPowerPolynomial a b d).homogenize (d + 1) =
      linearFormPolynomial ![a 1, a 0] * linearFormPolynomial ![b 1, b 0] ^ d := by
  apply Polynomial.homogenize_eq_of_isHomogeneous
  · simpa only [one_mul, Nat.add_comm] using
      (linearFormPolynomial_homogeneous ![a 1, a 0]).mul
        ((linearFormPolynomial_homogeneous ![b 1, b 0]).pow d)
  · have ha : ![a 0, a 1] = a := by funext i; fin_cases i <;> rfl
    have hb : ![b 0, b 1] = b := by funext i; fin_cases i <;> rfl
    simp only [map_mul, map_pow, binary_linear_form_dehomogenize,
      Matrix.cons_val_zero, Matrix.cons_val_one, segreRulingPowerPolynomial, ha, hb]

variable [CharZero E]

/-- An actual nonzero ruling polynomial over its original coefficient
field constructs its entire linear-times-dth-power factorization there,
even when an affine factor is constant or the two factors coincide. -/
theorem univariate_linear_times_power_factorization_descends
    (f : K →+* E) (P : Polynomial K) (hP0 : P ≠ 0)
    (a b : Fin 2 → E) (d : ℕ) (hd : 1 < d)
    (hP : P.map f = segreRulingPowerPolynomial a b d) :
    ∃ A B : Fin 2 → K, P = segreRulingPowerPolynomial A B d := by
  have hdegree : P.natDegree ≤ d + 1 := by
    rw [← Polynomial.natDegree_map f, hP]
    exact segreRulingPowerPolynomial_natDegree_le a b d
  have hhom0 : P.homogenize (d + 1) ≠ 0 := by
    exact fun h => hP0 ((Polynomial.homogenize_eq_zero_iff hdegree).mp h)
  have hhom : MvPolynomial.map f (P.homogenize (d + 1)) =
      linearFormPolynomial ![a 1, a 0] * linearFormPolynomial ![b 1, b 0] ^ d := by
    rw [← Polynomial.homogenize_map, hP, segre_ruling_power_polynomial_homogenize]
  obtain ⟨_j, B, A, _hbj, _hBj, _hB, _hA, hfactor⟩ :=
    binary_linear_times_power_factorization_descends f (P.homogenize (d + 1)) hhom0
      ![a 1, a 0] ![b 1, b 0] d hd hhom
  refine ⟨![A 1, A 0], ![B 1, B 0], ?_⟩
  have he := congrArg (MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial K)]) hfactor
  simpa only [Polynomial.aeval_homogenize_X_one P hdegree, map_mul, map_pow,
    binary_linear_form_dehomogenize, segreRulingPowerPolynomial] using he

/-- The descended ruling factors are nonzero original affine polynomials
of degree at most one, with an exact original-field identity. -/
theorem univariate_linear_times_power_constructs_original_linear_factors
    (f : K →+* E) (P : Polynomial K) (hP0 : P ≠ 0)
    (a b : Fin 2 → E) (d : ℕ) (hd : 1 < d)
    (hP : P.map f = segreRulingPowerPolynomial a b d) :
    ∃ A B : Polynomial K, A ≠ 0 ∧ B ≠ 0 ∧ A.natDegree ≤ 1 ∧ B.natDegree ≤ 1 ∧
      P = A * B ^ d := by
  obtain ⟨A, B, hfactor⟩ := univariate_linear_times_power_factorization_descends f P hP0 a b d hd hP
  refine ⟨segreRulingAffineFactor A, segreRulingAffineFactor B, ?_, ?_,
    segreRulingAffineFactor_natDegree_le_one A, segreRulingAffineFactor_natDegree_le_one B, hfactor⟩
  · intro h
    apply hP0
    simpa only [segreRulingPowerPolynomial, h, zero_mul] using hfactor
  · intro h
    apply hP0
    simpa only [segreRulingPowerPolynomial, h, zero_pow (by omega : d ≠ 0), mul_zero] using hfactor

end DimensionFourDependence
