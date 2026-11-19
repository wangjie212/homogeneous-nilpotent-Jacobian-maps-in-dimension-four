import DimensionFourDependence.VandermondeSubmodulePolarization
import DimensionFourDependence.QuadraticFlowElementaryParameters
import DimensionFourDependence.QuadraticFlowParameterConjugacy

/-! # Every polynomial invariant parameter gives a tame quadratic flow -/

namespace DimensionFourDependence.QuadraticFlow

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]

/-- Scalar-uniform tame parameters form a genuine vector subspace;
the additive group law of the actual automorphisms proves closure. -/
noncomputable def tameParameterSpace : Submodule K (MvPolynomial (Fin 3) K) where
  carrier := {h | ∀ c : K, automorphism4 (c • h) ∈ Tame.subgroup K 4}
  zero_mem' := by
    intro c
    rw [smul_zero, automorphism4_zero]
    exact (Tame.subgroup K 4).one_mem
  add_mem' := by
    intro h k hh hk c
    rw [smul_add, automorphism4_add]
    exact (Tame.subgroup K 4).mul_mem (hh c) (hk c)
  smul_mem' := by
    intro c h hh d
    rw [smul_smul]
    exact hh (d * c)

/-- Every scalar multiple of a polarized auxiliary power is an actual
elementary-shear conjugate of a two-elementary-factor quadratic flow. -/
theorem shifted_auxiliary_power_mem_tameParameterSpace
    (m N : ℕ) (r : K) :
    X 2 ^ m * (X 1 + C r * X 0) ^ N ∈ tameParameterSpace (K := K) := by
  intro c
  let f : MvPolynomial (Fin 2) K := C c * X 1 ^ m * X 0 ^ N
  have h := automorphism4_parameter_shift_tame r (aeval ![X 1, X 2] f)
    (automorphism4_auxiliary_only_tame f)
  have he : parameterShift3 r (aeval ![X 1, X 2] f) =
      c • (X 2 ^ m * (X 1 + C r * X 0) ^ N) := by
    simp only [f, parameterShift3, map_mul, map_pow, aeval_C, algebraMap_eq,
      aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      MvPolynomial.smul_eq_C_mul]
    simp
    ring
  rw [he] at h
  exact h

variable [CharZero K]

/-- The actual finite Vandermonde polarization puts every parameter
monomial into the scalar-uniform tame parameter subspace. -/
theorem parameter_monomial_mem_tameParameterSpace (k l m : ℕ) :
    X 2 ^ m * X 1 ^ l * X 0 ^ k ∈ tameParameterSpace (K := K) := by
  have h := submodule_contains_binary_monomial_of_shifted_powers
    (tameParameterSpace (K := K)) (X 2 ^ m) (X 1) (X 0) (k + l)
    (fun r => by simpa only [MvPolynomial.algebraMap_eq] using
      shifted_auxiliary_power_mem_tameParameterSpace (K := K) m (k + l) r)
    k (by omega)
  simpa only [Nat.add_sub_cancel_left] using h

/-- Every actual invariant parameter has a tame flow in four
variables over the original characteristic-zero field. No extra
coordinate or polynomial factorization hypothesis is supplied. -/
theorem automorphism4_tame (h : MvPolynomial (Fin 3) K) :
    automorphism4 h ∈ Tame.subgroup K 4 := by
  classical
  have hm : h ∈ tameParameterSpace (K := K) := by
    rw [h.as_sum]
    apply (tameParameterSpace (K := K)).sum_mem
    intro d hd
    have hmono : monomial d (h.coeff d) =
        (h.coeff d) • (X 2 ^ d 2 * X 1 ^ d 1 * X 0 ^ d 0) := by
      rw [MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul]
      congr 1
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
      ring
    rw [hmono]
    exact (tameParameterSpace (K := K)).smul_mem _
      (parameter_monomial_mem_tameParameterSpace (d 0) (d 1) (d 2))
  have h1 := hm (1 : K)
  simpa only [one_smul] using h1

end DimensionFourDependence.QuadraticFlow
