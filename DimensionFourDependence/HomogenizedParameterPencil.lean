import DimensionFourDependence.HomogeneousEvaluationScaling
import Mathlib.Algebra.Polynomial.Homogenize

/-! # Exact polynomial clearing and specialization of a homogeneous source pencil -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K A B : Type*} [Field K] [CommRing A] [Algebra K A]
  [CommRing B] [Algebra K B]

/-- The actual homogeneous polynomial numerator of a univariate
parameter polynomial evaluated at the source pencil `p/q`. -/
noncomputable def homogeneousParameterPolynomialValue
    (v : Polynomial K) (N : ℕ) (p q : A) : A :=
  aeval ![p, q] (v.homogenize N)

/-- Homogeneous parameter evaluation commutes with every coefficient
algebra homomorphism, including actual quotient maps of the source. -/
theorem homogeneousParameterPolynomialValue_algHom
    (f : A →ₐ[K] B) (v : Polynomial K) (N : ℕ) (p q : A) :
    f (homogeneousParameterPolynomialValue v N p q) =
      homogeneousParameterPolynomialValue v N (f p) (f q) := by
  have he := comp_aeval_apply (![p, q] : Fin 2 → A) f (v.homogenize N)
  have hpoint : (fun i : Fin 2 => f (![p, q] i)) = ![f p, f q] := by
    funext i
    fin_cases i <;> rfl
  exact he.trans (congrArg (fun x => aeval x (v.homogenize N)) hpoint)

/-- At a literal constant pencil ratio, the homogenized parameter
polynomial is its scalar value times the exact denominator power. -/
theorem homogeneousParameterPolynomialValue_proportional
    (v : Polynomial K) {N : ℕ} (hv : v.natDegree ≤ N) (a : K) (q : A) :
    homogeneousParameterPolynomialValue v N (algebraMap K A a * q) q =
      q ^ N * algebraMap K A (v.eval a) := by
  have hpoint : (![algebraMap K A a * q, q] : Fin 2 → A) =
      fun i => q * (![algebraMap K A a, 1] : Fin 2 → A) i := by
    funext i
    fin_cases i <;> simp [mul_comm]
  rw [homogeneousParameterPolynomialValue, hpoint,
    homogeneous_aeval_scale _ (Polynomial.isHomogeneous_homogenize v) _ q,
    Polynomial.aeval_homogenize_of_eq_one hv _ (by rfl)]
  change q ^ N * Polynomial.aeval (algebraMap K A a) v = _
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

variable {E : Type*} [Field E] [Algebra K E]

/-- In a field, the polynomial numerator is exactly the denominator
power times the original parameter evaluation. -/
theorem homogeneousParameterPolynomialValue_fraction
    (v : Polynomial K) {N : ℕ} (hv : v.natDegree ≤ N) (p q : E) (hq : q ≠ 0) :
    homogeneousParameterPolynomialValue v N p q = q ^ N * Polynomial.aeval (p / q) v := by
  have hpoint : (![p, q] : Fin 2 → E) =
      fun i => q * (![p / q, 1] : Fin 2 → E) i := by
    funext i
    fin_cases i
    · change p = q * (p / q)
      field_simp
    · simp
  rw [homogeneousParameterPolynomialValue, hpoint,
    homogeneous_aeval_scale _ (Polynomial.isHomogeneous_homogenize v) _ q,
    Polynomial.aeval_homogenize_of_eq_one hv _ (by rfl)]
  rfl

variable {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K

/-- The exact homogeneous numerator has the expected literal
remainder modulo every actual source pencil equation `p-aq`. -/
theorem source_pencil_divides_homogeneous_parameter_remainder
    (v : Polynomial K) {N : ℕ} (hv : v.natDegree ≤ N) (p q : R₀) (a : K) :
    p - C a * q ∣ homogeneousParameterPolynomialValue v N p q - q ^ N * C (v.eval a) := by
  let I : Ideal R₀ := Ideal.span {p - C a * q}
  let f : R₀ →ₐ[K] R₀ ⧸ I := Ideal.Quotient.mkₐ K I
  have hC (c : K) : f (C c) = algebraMap K (R₀ ⧸ I) c := f.commutes c
  have hratio : f p = algebraMap K (R₀ ⧸ I) a * f q := by
    have he : f (p - C a * q) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    simpa only [map_sub, map_mul, hC, sub_eq_zero] using he
  have he : f (homogeneousParameterPolynomialValue v N p q - q ^ N * C (v.eval a)) = 0 := by
    rw [map_sub, homogeneousParameterPolynomialValue_algHom, hratio,
      homogeneousParameterPolynomialValue_proportional v hv a,
      map_mul, map_pow, hC, sub_self]
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)

end DimensionFourDependence
