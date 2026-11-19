import DimensionFourDependence.IteratedDerivationPolynomial
import Mathlib.RingTheory.Derivation.MapCoeffs

/-! # Actual coefficient derivatives and polynomial comparison over exact constants -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]

/-- Apply the actual ambient derivation to each original polynomial coefficient. -/
noncomputable def coefficientPolynomialDerivation (D : Derivation K E E) :
    Derivation K (Polynomial E) (Polynomial E) :=
  PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs

@[simp]
theorem coefficientPolynomialDerivation_coeff (D : Derivation K E E) (P : Polynomial E) (i : ℕ) :
    (coefficientPolynomialDerivation D P).coeff i = D (P.coeff i) := rfl

@[simp]
theorem coefficientPolynomialDerivation_monomial (D : Derivation K E E) (n : ℕ) (a : E) :
    coefficientPolynomialDerivation D (Polynomial.monomial n a) = Polynomial.monomial n (D a) := by
  ext i
  by_cases h : n = i <;>
    simp only [coefficientPolynomialDerivation_coeff, Polynomial.coeff_monomial, h, ite_true, ite_false, map_zero]

/-- Iterating the actual coefficient derivative iterates that same
ambient derivative on every original coefficient. -/
theorem coefficientPolynomialDerivation_iterate_coeff
    (D : Derivation K E E) (n : ℕ) (P : Polynomial E) (i : ℕ) :
    (((coefficientPolynomialDerivation D : Polynomial E → Polynomial E)^[n]) P).coeff i =
      (D : E → E)^[n] (P.coeff i) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', coefficientPolynomialDerivation_coeff, ih]

/-- A fixed actual evaluation coordinate allows the coefficient
and ambient derivatives to be compared directly. -/
theorem coefficientPolynomialDerivation_eval
    (D : Derivation K E E) (s : E) (hs : D s = 0) (P : Polynomial E) :
    D (P.eval s) = (coefficientPolynomialDerivation D P).eval s := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.eval_add, map_add, hP, hQ]
  | monomial n a =>
    simp [Polynomial.eval_monomial, D.leibniz, D.leibniz_pow, hs, smul_eq_mul, mul_comm]

/-- The same actual coefficient/evaluation comparison holds after
arbitrarily many derivatives, with no coordinate change. -/
theorem coefficientPolynomialDerivation_iterate_eval
    (D : Derivation K E E) (s : E) (hs : D s = 0) (P : Polynomial E) (n : ℕ) :
    (D : E → E)^[n] (P.eval s) =
      (((coefficientPolynomialDerivation D : Polynomial E → Polynomial E)^[n]) P).eval s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      coefficientPolynomialDerivation_eval D s hs]

/-- Actual derivative-constant coefficients form a polynomial over
the actual constant subfield, retaining its original coefficient vector
and exact degree. -/
theorem polynomial_constructs_derivation_constant_coefficients
    (D : Derivation K E E) (P : Polynomial E) (hcoeff : ∀ i, D (P.coeff i) = 0) :
    ∃ Q : Polynomial (derivationConstants D),
      Q.map (algebraMap (derivationConstants D) E) = P ∧ Q.natDegree = P.natDegree := by
  classical
  let J := derivationConstants D
  let Q : Polynomial J := ∑ i ∈ P.support, Polynomial.monomial i ⟨P.coeff i, hcoeff i⟩
  have hmap : Q.map (algebraMap J E) = P := by
    simp only [Q, Polynomial.map_sum, Polynomial.map_monomial]
    exact P.sum_monomial_eq
  refine ⟨Q, hmap, ?_⟩
  rw [← Polynomial.natDegree_map (algebraMap J E), hmap]

/-- A coordinate with derivative one detects every original polynomial
relation whose actual coefficients are derivative constants. -/
theorem polynomial_constant_coefficients_eval_zero_implies_zero
    (D : Derivation K E E) (s : E) (hs : D s = 1) (P : Polynomial E)
    (hcoeff : ∀ i, D (P.coeff i) = 0) (hzero : P.eval s = 0) : P = 0 := by
  let J := derivationConstants D
  let : CharZero J := charZero_of_injective_algebraMap (algebraMap K J).injective
  let δ := derivationOverConstantSubfield D J le_rfl
  have htrans : Transcendental J s := by
    intro ha
    have hz := derivation_zero_of_isAlgebraic δ s ha
    exact one_ne_zero (hs.symm.trans hz)
  obtain ⟨Q, hmap, _hdegree⟩ := polynomial_constructs_derivation_constant_coefficients D P hcoeff
  have hval : Polynomial.aeval s Q = 0 := by
    rw [← hmap, Polynomial.eval_map] at hzero
    exact hzero
  have hQ : Q = 0 := by
    apply (transcendental_iff_injective.mp htrans)
    rw [map_zero]
    exact hval
  rw [← hmap, hQ, Polynomial.map_zero]

/-- A polynomial of degree at most N in an actual coordinate has zero
(N+1)st derivative when all its actual coefficients are constants. -/
theorem constant_coefficient_polynomial_iterated_derivative_zero
    (D : Derivation K E E) (t : E) (ht : D t = 1) (P : Polynomial E)
    (hcoeff : ∀ i, D (P.coeff i) = 0) (N : ℕ) (hdegree : P.natDegree ≤ N) :
    (D : E → E)^[N + 1] (P.eval t) = 0 := by
  let J := derivationConstants D
  let : CharZero J := charZero_of_injective_algebraMap (algebraMap K J).injective
  let δ := derivationOverConstantSubfield D J le_rfl
  obtain ⟨Q, hmap, hdegreeQ⟩ := polynomial_constructs_derivation_constant_coefficients D P hcoeff
  have hQzero : Polynomial.derivative^[N + 1] Q = 0 :=
    Polynomial.iterate_derivative_eq_zero (hdegreeQ.le.trans hdegree |>.trans_lt (Nat.lt_succ_self N))
  have hv : Polynomial.aeval t Q = P.eval t := by
    rw [← hmap, Polynomial.eval_map]
    rfl
  have he := derivation_iterated_polynomial_evaluation δ t ht Q (N + 1)
  rw [hQzero, map_zero] at he
  change (D : E → E)^[N + 1] (Polynomial.aeval t Q) = 0 at he
  rw [hv] at he
  exact he

end DimensionFourDependence
