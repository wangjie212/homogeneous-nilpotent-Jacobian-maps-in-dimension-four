import DimensionFourDependence.PowerRemainderUniqueness
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! # A polynomial square equal to a scalar irreducible power has even exponent -/

namespace DimensionFourDependence

open MvPolynomial UniqueFactorizationMonoid

set_option maxHeartbeats 2500000

variable {K σ : Type*} [Field K]

/-- Exact original prime multiplicities construct the even exponent
and the polynomial square root. The unit is an original nonzero scalar;
no square-root scalar or factorization is supplied. -/
theorem scalar_irreducible_power_square_constructs_half_power
    (P Q : MvPolynomial σ K) (hQ : Irreducible Q) (γ : K) (hγ : γ ≠ 0) (d : ℕ)
    (he : P ^ 2 = MvPolynomial.C γ * Q ^ d) :
    ∃ (m : ℕ) (κ : K), d = 2 * m ∧ κ ≠ 0 ∧ P = κ • Q ^ m := by
  classical
  letI : NormalizedGCDMonoid (MvPolynomial σ K) :=
    Classical.arbitrary (NormalizedGCDMonoid (MvPolynomial σ K))
  have hP : P ≠ 0 := by
    intro hz
    have he' := he
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at he'
    exact (mul_ne_zero (MvPolynomial.C_ne_zero.mpr hγ) (pow_ne_zero d hQ.ne_zero)) he'.symm
  have hunit : IsUnit (MvPolynomial.C γ : MvPolynomial σ K) :=
    (isUnit_iff_ne_zero.mpr hγ).map MvPolynomial.C
  have hunitFactor : factorization (MvPolynomial.C γ : MvPolynomial σ K) = 0 := by
    rw [factorization_eq_of_associated _ 1 (associated_one_iff_isUnit.mpr hunit), factorization_one]
  have hfactor : 2 • factorization P = d • factorization Q := by
    have hf := congrArg factorization he
    rw [factorization_pow, factorization_mul (MvPolynomial.C_ne_zero.mpr hγ)
      (pow_ne_zero d hQ.ne_zero), hunitFactor, zero_add, factorization_pow] at hf
    exact hf
  have hQone : factorization Q (normalize Q) = 1 := by
    simp only [factorization_eq_count, normalizedFactors_irreducible hQ, Multiset.count_singleton]
    simp
  let m := factorization P (normalize Q)
  have hd : d = 2 * m := by
    have hf := congrArg (fun a : MvPolynomial σ K →₀ ℕ => a (normalize Q)) hfactor
    simp only [Finsupp.smul_apply, smul_eq_mul, hQone, mul_one] at hf
    exact hf.symm
  have heq : factorization P = factorization (Q ^ m) := by
    rw [factorization_pow]
    ext p
    have hf := congrArg (fun a : MvPolynomial σ K →₀ ℕ => a p) hfactor
    simp only [Finsupp.smul_apply, smul_eq_mul] at hf ⊢
    rw [hd] at hf
    nlinarith
  obtain ⟨u, hu⟩ := (associated_of_factorization_eq P (Q ^ m) hP
    (pow_ne_zero m hQ.ne_zero) heq).symm
  obtain ⟨κ, hκunit, huC⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp (Units.isUnit u)
  refine ⟨m, κ, hd, isUnit_iff_ne_zero.mp hκunit, ?_⟩
  simpa only [huC, smul_eq_C_mul, mul_comm] using hu.symm

end DimensionFourDependence
