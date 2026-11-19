import DimensionFourDependence.HomogenizedParameterPencil
import DimensionFourDependence.QuasiTranslationFiberDivisorTangency

/-! # Primitive polynomial parameter vectors remain primitive after a reduced pencil -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The parameter value at infinity is the exact top coefficient,
including the case where the chosen homogenizing degree is larger. -/
theorem homogeneousParameterPolynomialValue_second_zero
    (v : Polynomial K) (N : ℕ) (p : A) :
    homogeneousParameterPolynomialValue v N p 0 = algebraMap K A (v.coeff N) * p ^ N := by
  induction v using Polynomial.induction_on' with
  | add v w hv hw =>
    simp only [homogeneousParameterPolynomialValue, Polynomial.homogenize_add,
      map_add, Polynomial.coeff_add] at hv hw ⊢
    rw [hv, hw, add_mul]
  | monomial m c =>
    by_cases hm : m ≤ N
    · rw [homogeneousParameterPolynomialValue, ← Polynomial.C_mul_X_pow_eq_monomial,
        Polynomial.homogenize_C_mul, Polynomial.homogenize_X_pow hm]
      simp only [map_mul, map_pow, aeval_C, aeval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow]
      by_cases hmn : m = N
      · subst m
        simp
      · have hd : N - m ≠ 0 := by omega
        simp [Ne.symm hmn, zero_pow hd]
    · rw [homogeneousParameterPolynomialValue,
        Polynomial.homogenize_monomial_of_lt (by omega), map_zero]
      simp [Polynomial.coeff_monomial, show m ≠ N by omega]

variable {m n : ℕ}

/-- A primitive univariate polynomial vector has no common finite
parameter zero over the original coefficient field. -/
theorem primitive_univariate_polynomial_vector_eval_ne_zero
    (v : Fin m → Polynomial K)
    (hprim : ∀ f : Polynomial K, (∀ i, f ∣ v i) → IsUnit f) (a : K) :
    (fun i => (v i).eval a) ≠ 0 := by
  intro hz
  apply Polynomial.not_isUnit_X_sub_C a
  apply hprim
  intro i
  exact Polynomial.dvd_iff_isRoot.mpr (congrFun hz i)

local notation "R₀" => MvPolynomial (Fin n) K
local notation "F₀" => FractionRing (MvPolynomial (Fin n) K)

/-- At a transcendental reduced source ratio the homogeneous parameter
vector is nonzero. No geometric generic point is supplied. -/
theorem homogenized_parameter_vector_nonzero_of_transcendental_ratio
    (v : Fin m → Polynomial K) (hv : v ≠ 0) {N : ℕ}
    (hN : ∀ i, (v i).natDegree ≤ N) (p q : R₀) (hq : q ≠ 0)
    (ht : Transcendental K (algebraMap R₀ F₀ p / algebraMap R₀ F₀ q)) :
    (fun i => homogeneousParameterPolynomialValue (v i) N p q) ≠ 0 := by
  intro hz
  apply hv
  funext i
  have he := congrArg (IsScalarTower.toAlgHom K R₀ F₀) (congrFun hz i)
  rw [homogeneousParameterPolynomialValue_algHom, Pi.zero_apply, map_zero] at he
  change homogeneousParameterPolynomialValue (v i) N (algebraMap R₀ F₀ p)
    (algebraMap R₀ F₀ q) = 0 at he
  rw [
    homogeneousParameterPolynomialValue_fraction (v i) (hN i) _ _
      (fun h => hq (IsFractionRing.injective R₀ F₀ (h.trans (map_zero _).symm)))] at he
  have hval : Polynomial.aeval (algebraMap R₀ F₀ p / algebraMap R₀ F₀ q) (v i) = 0 :=
    (mul_eq_zero.mp he).resolve_left (pow_ne_zero N
      (fun h => hq (IsFractionRing.injective R₀ F₀ (h.trans (map_zero _).symm))))
  exact (transcendental_iff_injective.mp ht) (hval.trans (map_zero _).symm)

variable [IsAlgClosed K]

/-- The entire common-zero locus of the homogenized vector is
contained in the base locus of the original pencil. Both finite
parameter values and the value at infinity are treated. -/
theorem homogenized_primitive_parameter_common_zero_forces_pencil_base_point
    (v : Fin m → Polynomial K)
    (hprim : ∀ f : Polynomial K, (∀ i, f ∣ v i) → IsUnit f)
    {N : ℕ} (hN : ∀ i, (v i).natDegree ≤ N)
    (htop : ∃ i, (v i).coeff N ≠ 0) (p q : R₀) (z : Fin n → K)
    (hz : ∀ i, aeval z (homogeneousParameterPolynomialValue (v i) N p q) = 0) :
    aeval z p = 0 ∧ aeval z q = 0 := by
  have hq : aeval z q = 0 := by
    by_contra hq
    apply primitive_univariate_polynomial_vector_eval_ne_zero v hprim (aeval z p / aeval z q)
    funext i
    have hi := hz i
    rw [homogeneousParameterPolynomialValue_algHom,
      homogeneousParameterPolynomialValue_fraction (v i) (hN i) _ _ hq] at hi
    exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero N hq)
  refine ⟨?_, hq⟩
  obtain ⟨i, hi⟩ := htop
  have he := hz i
  rw [homogeneousParameterPolynomialValue_algHom, hq,
    homogeneousParameterPolynomialValue_second_zero] at he
  have hpN : aeval z p ^ N = 0 := (mul_eq_zero.mp he).resolve_left (by simpa using hi)
  exact eq_zero_of_pow_eq_zero hpN

/-- A primitive polynomial parameter vector, homogenized to its exact
maximal degree and evaluated at a reduced source pencil, is primitive
in the actual multivariate polynomial source. -/
theorem reduced_pencil_homogenized_primitive_parameter_vector_isPrimitive
    (v : Fin m → Polynomial K)
    (hprim : ∀ f : Polynomial K, (∀ i, f ∣ v i) → IsUnit f)
    {N : ℕ} (hN : ∀ i, (v i).natDegree ≤ N)
    (htop : ∃ i, (v i).coeff N ≠ 0) (p q : R₀) (hrel : IsRelPrime p q)
    (hW : (fun i => homogeneousParameterPolynomialValue (v i) N p q) ≠ 0) :
    IsPrimitiveVec (fun i => homogeneousParameterPolynomialValue (v i) N p q) := by
  classical
  intro f hf
  by_contra hunit
  have hf0 : f ≠ 0 := by
    intro hz
    apply hW
    funext i
    exact zero_dvd_iff.mp (hz ▸ hf i)
  obtain ⟨δ, hδ, hδf⟩ := WfDvdMonoid.exists_irreducible_factor hunit hf0
  have hδprime : Prime δ := UniqueFactorizationMonoid.irreducible_iff_prime.mp hδ
  have hδW (i) : δ ∣ homogeneousParameterPolynomialValue (v i) N p q := hδf.trans (hf i)
  have hbase (z : Fin n → K) (hz : aeval z δ = 0) : aeval z p = 0 ∧ aeval z q = 0 := by
    apply homogenized_primitive_parameter_common_zero_forces_pencil_base_point v hprim hN htop p q z
    intro i
    obtain ⟨b, hb⟩ := hδW i
    rw [hb, map_mul, hz, zero_mul]
  have hδp : δ ∣ p := squarefree_polynomial_divides_of_vanishing_on_its_zero_locus
    δ p hδprime.squarefree (fun z hz => (hbase z hz).1)
  have hδq : δ ∣ q := squarefree_polynomial_divides_of_vanishing_on_its_zero_locus
    δ q hδprime.squarefree (fun z hz => (hbase z hz).2)
  exact hδ.not_isUnit (hrel hδp hδq)

end DimensionFourDependence
