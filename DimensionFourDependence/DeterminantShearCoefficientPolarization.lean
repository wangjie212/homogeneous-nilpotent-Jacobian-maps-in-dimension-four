import DimensionFourDependence.DeterminantShearCoefficientConjugacy
import DimensionFourDependence.VandermondeSubmodulePolarization

/-! # The finite coefficient polarization in the second half of Lemma 6.2 -/

namespace DimensionFourDependence.DeterminantShear

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]

noncomputable def tameParameterSpace : Submodule K (MvPolynomial (Fin 3) K) where
  carrier := {f | ∀ c : K, automorphism4 (c • f) ∈ Tame.subgroup K 4}
  zero_mem' := by
    intro c
    rw [smul_zero, automorphism4_zero]
    exact (Tame.subgroup K 4).one_mem
  add_mem' := by
    intro f g hf hg c
    rw [smul_add, automorphism4_add]
    exact (Tame.subgroup K 4).mul_mem (hf c) (hg c)
  smul_mem' := by
    intro c f hf d
    rw [smul_smul]
    exact hf (d * c)

theorem polarized_coefficient_power_mem_tameParameterSpace
    (hbase : ∀ f : MvPolynomial (Fin 2) K,
      automorphism4 (aeval ![X 0, X 1] f) ∈ Tame.subgroup K 4)
    (m N : ℕ) (r : K) :
    X 0 ^ m * (X 1 + C r * X 2) ^ N ∈ tameParameterSpace (K := K) := by
  intro c
  let f : MvPolynomial (Fin 2) K := C c * X 0 ^ m * X 1 ^ N
  have h := automorphism4_coefficient_shift_tame r (aeval ![X 0, X 1] f) (hbase f)
  have he : coefficientParameterShift3 r (aeval ![X 0, X 1] f) =
      c • (X 0 ^ m * (X 1 + C r * X 2) ^ N) := by
    simp only [f, coefficientParameterShift3, map_mul, map_pow, aeval_C, algebraMap_eq,
      aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      MvPolynomial.smul_eq_C_mul]
    ring
  rw [he] at h
  exact h

variable [CharZero K]

/-- The alpha-only case constructs every mixed coefficient monomial
through a finite Vandermonde calculation over the original field. -/
theorem coefficient_monomial_mem_tameParameterSpace
    (hbase : ∀ f : MvPolynomial (Fin 2) K,
      automorphism4 (aeval ![X 0, X 1] f) ∈ Tame.subgroup K 4)
    (m l k : ℕ) :
    X 0 ^ m * X 1 ^ l * X 2 ^ k ∈ tameParameterSpace (K := K) := by
  have h := submodule_contains_binary_monomial_of_shifted_powers
    (tameParameterSpace (K := K)) (X 0 ^ m) (X 1) (X 2) (k + l)
    (fun r => by simpa only [MvPolynomial.algebraMap_eq] using
      polarized_coefficient_power_mem_tameParameterSpace hbase m (k + l) r)
    k (by omega)
  simpa only [Nat.add_sub_cancel_left] using h

/-- Exact assembly of the second polarization step. The alpha-only
input remains explicit until it is supplied by the two quadratic flows. -/
theorem automorphism4_tame_of_alpha_only
    (hbase : ∀ f : MvPolynomial (Fin 2) K,
      automorphism4 (aeval ![X 0, X 1] f) ∈ Tame.subgroup K 4)
    (f : MvPolynomial (Fin 3) K) : automorphism4 f ∈ Tame.subgroup K 4 := by
  classical
  have hm : f ∈ tameParameterSpace (K := K) := by
    rw [f.as_sum]
    apply (tameParameterSpace (K := K)).sum_mem
    intro d hd
    have hmono : monomial d (f.coeff d) =
        (f.coeff d) • (X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 2) := by
      rw [MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul]
      congr 1
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
    rw [hmono]
    exact (tameParameterSpace (K := K)).smul_mem _
      (coefficient_monomial_mem_tameParameterSpace hbase (d 0) (d 1) (d 2))
  have h1 := hm (1 : K)
  simpa only [one_smul] using h1

end DimensionFourDependence.DeterminantShear
