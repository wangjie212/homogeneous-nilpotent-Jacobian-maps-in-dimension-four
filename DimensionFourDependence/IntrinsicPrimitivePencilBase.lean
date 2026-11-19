import DimensionFourDependence.PrimitiveHomogenizedParameterVector
import DimensionFourDependence.PrimitiveBinaryDirection

/-! # The source pencil base is intrinsically determined by its primitive evaluated vector -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] {m n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K

/-- A positive homogeneous source form in any finite source
dimension is not a unit. -/
theorem positive_source_homogeneous_form_not_unit
    (p : R₀) {D : ℕ} (hD : 0 < D) (hp : p.IsHomogeneous D) : ¬IsUnit p := by
  intro hu
  have hz := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
  rw [hp.totalDegree hu.ne_zero] at hz
  omega

/-- The denominator divides a homogenized parameter value when its
exact top coefficient vanishes. This holds in the original source
ring even if the actual chosen homogenizing degree is too large. -/
theorem source_pencil_denominator_divides_parameter_value_of_top_coeff_zero
    (v : Polynomial K) (N : ℕ) (p q : R₀) (hv : v.coeff N = 0) :
    q ∣ homogeneousParameterPolynomialValue v N p q := by
  let I : Ideal R₀ := Ideal.span {q}
  let f : R₀ →ₐ[K] R₀ ⧸ I := Ideal.Quotient.mkₐ K I
  have hq : f q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton q))
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f (homogeneousParameterPolynomialValue v N p q) = 0
  rw [homogeneousParameterPolynomialValue_algHom, hq,
    homogeneousParameterPolynomialValue_second_zero, hv, map_zero, zero_mul]

/-- Primitivity of the actual evaluated source vector forces a
nonzero top parameter coefficient. No parameter-primitivity or
exact-degree hypothesis is supplied. -/
theorem primitive_evaluated_positive_pencil_constructs_nonzero_top_parameter_coefficient
    (v : Fin m → Polynomial K) (N : ℕ) (p q : R₀) {D : ℕ} (hD : 0 < D)
    (hqH : q.IsHomogeneous D)
    (hprim : ∀ r : R₀, (∀ i, r ∣ homogeneousParameterPolynomialValue (v i) N p q) → IsUnit r) :
    ∃ i, (v i).coeff N ≠ 0 := by
  by_contra hn
  push Not at hn
  exact positive_source_homogeneous_form_not_unit q hD hqH
    (hprim q (fun i => source_pencil_denominator_divides_parameter_value_of_top_coeff_zero
      (v i) N p q (hn i)))

/-- Primitivity of the evaluated positive homogeneous source pencil
excludes every common finite parameter root over the original field. -/
theorem primitive_evaluated_positive_pencil_parameter_values_have_no_common_root
    (v : Fin m → Polynomial K) {N : ℕ} (hN : ∀ i, (v i).natDegree ≤ N)
    (p q : R₀) {D : ℕ} (hD : 0 < D) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (hprim : ∀ r : R₀, (∀ i, r ∣ homogeneousParameterPolynomialValue (v i) N p q) → IsUnit r)
    (a : K) : ∃ i, (v i).eval a ≠ 0 := by
  by_contra hn
  push Not at hn
  have hdiv (i) : p - C a * q ∣ homogeneousParameterPolynomialValue (v i) N p q := by
    simpa only [hn i, map_zero, mul_zero, sub_zero] using
      source_pencil_divides_homogeneous_parameter_remainder (v i) (hN i) p q a
  exact positive_source_homogeneous_form_not_unit (p - C a * q) hD
    (hpH.sub (hqH.C_mul a)) (hprim _ hdiv)

/-- The whole actual common-zero locus of a primitive evaluated
positive pencil is exactly supported on its original source base.
This derives the needed finite and infinite parameter assertions from
evaluated primitivity alone. -/
theorem primitive_evaluated_positive_pencil_common_zero_forces_source_base
    (v : Fin m → Polynomial K) {N : ℕ} (hN : ∀ i, (v i).natDegree ≤ N)
    (p q : R₀) {D : ℕ} (hD : 0 < D) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (hprim : ∀ r : R₀, (∀ i, r ∣ homogeneousParameterPolynomialValue (v i) N p q) → IsUnit r)
    (z : Fin n → K) (hz : ∀ i, aeval z (homogeneousParameterPolynomialValue (v i) N p q) = 0) :
    aeval z p = 0 ∧ aeval z q = 0 := by
  have hq : aeval z q = 0 := by
    by_contra hq
    obtain ⟨i, hi⟩ := primitive_evaluated_positive_pencil_parameter_values_have_no_common_root
      v hN p q hD hpH hqH hprim (aeval z p / aeval z q)
    have he := hz i
    rw [homogeneousParameterPolynomialValue_algHom,
      homogeneousParameterPolynomialValue_fraction (v i) (hN i) _ _ hq] at he
    have hv : Polynomial.aeval (aeval z p / aeval z q) (v i) = 0 :=
      (mul_eq_zero.mp he).resolve_left (pow_ne_zero N hq)
    exact hi (by simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using hv)
  obtain ⟨i, hi⟩ := primitive_evaluated_positive_pencil_constructs_nonzero_top_parameter_coefficient
    v N p q hD hqH hprim
  have he := hz i
  rw [homogeneousParameterPolynomialValue_algHom, hq,
    homogeneousParameterPolynomialValue_second_zero] at he
  have hpN : aeval z p ^ N = 0 := (mul_eq_zero.mp he).resolve_left (by simpa using hi)
  exact ⟨eq_zero_of_pow_eq_zero hpN, hq⟩

variable [IsAlgClosed K]

/-- Any actual prime containing every primitive evaluated source
component contains both original pencil generators. Nullstellensatz
is applied to that actual prime; no equality of chosen parameter pairs
or supplied equality of pencil base loci is assumed. -/
theorem prime_contains_primitive_evaluated_positive_pencil_iff_contains_source_generators
    (v : Fin m → Polynomial K) {N : ℕ} (hNpos : 0 < N) (hN : ∀ i, (v i).natDegree ≤ N)
    (p q : R₀) {D : ℕ} (hD : 0 < D) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (hprim : ∀ r : R₀, (∀ i, r ∣ homogeneousParameterPolynomialValue (v i) N p q) → IsUnit r)
    (Q : Ideal R₀) [Q.IsPrime] :
    (∀ i, homogeneousParameterPolynomialValue (v i) N p q ∈ Q) ↔ p ∈ Q ∧ q ∈ Q := by
  constructor
  · intro hQ
    have hbase (z : Fin n → K) (hz : z ∈ zeroLocus K Q) : aeval z p = 0 ∧ aeval z q = 0 :=
      primitive_evaluated_positive_pencil_common_zero_forces_source_base v hN p q hD hpH hqH hprim z
        (fun i => hz _ (hQ i))
    have hp : p ∈ vanishingIdeal K (zeroLocus K Q) := fun z hz => (hbase z hz).1
    have hq : q ∈ vanishingIdeal K (zeroLocus K Q) := fun z hz => (hbase z hz).2
    rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hp hq
    exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩ i
    have hrem : p ∣ homogeneousParameterPolynomialValue (v i) N p q - q ^ N * C ((v i).coeff 0) := by
      simpa only [map_zero, zero_mul, sub_zero, ← Polynomial.coeff_zero_eq_eval_zero] using
        source_pencil_divides_homogeneous_parameter_remainder (v i) (hN i) p q 0
    obtain ⟨b, hb⟩ := hrem
    have hremQ : homogeneousParameterPolynomialValue (v i) N p q - q ^ N * C ((v i).coeff 0) ∈ Q := by
      rw [hb]
      exact Q.mul_mem_right b hp
    simpa only [sub_add_cancel] using Q.add_mem hremQ
      (Q.mul_mem_right (C ((v i).coeff 0)) (Q.pow_mem_of_mem hq N hNpos))

end DimensionFourDependence
