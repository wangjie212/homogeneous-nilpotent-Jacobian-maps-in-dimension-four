import DimensionFourDependence.DvrOrderQuotientLength
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-! # A general section's local order is bounded by its base norm

The element may be any regular function in the finite normalization,
including one absent from the original coordinate algebra. Relative
ideal norms take its prime-power membership into the same base-ideal
power. The base DVR quotient length therefore bounds its local order.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {R S : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.Free R S]

/-- Every local order bound for an arbitrary normalization element
implies the same base-ideal power bound for its actual algebra norm. -/
theorem finite_dedekind_norm_mem_base_prime_pow
    (p : Ideal R) [p.IsMaximal] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (z : S) (a : ℕ)
    (horder : algebraMap S (Localization.AtPrime q) z ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a) :
    Algebra.norm R z ∈ p ^ a := by
  let : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q p
  have hq : z ∈ q ^ a := by
    have h : z ∈ ((IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a).under S := horder
    rwa [IsLocalization.AtPrime.under_maximalIdeal_pow q (Localization.AtPrime q) a] at h
  have hn := Ideal.norm_mem_relNorm R (q ^ a) hq
  rw [map_pow] at hn
  have hle : Ideal.relNorm R q ≤ p := by
    exact (Ideal.relNorm_le_comap R q).trans_eq (Ideal.LiesOver.over (P := q) (p := p)).symm
  have hpow : ∀ n : ℕ, (Ideal.relNorm R q) ^ n ≤ p ^ n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      simp only [pow_succ]
      exact Ideal.mul_mono ih hle
  exact hpow a hn

variable [IsDiscreteValuationRing R]

/-- Every local order bound for an arbitrary normalization element
implies the same maximal-ideal power bound for its base norm. -/
theorem finite_dedekind_norm_mem_base_maximal_pow
    (q : Ideal S) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)]
    (z : S) (a : ℕ)
    (horder : algebraMap S (Localization.AtPrime q) z ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a) :
    Algebra.norm R z ∈ (IsLocalRing.maximalIdeal R) ^ a :=
  finite_dedekind_norm_mem_base_prime_pow (IsLocalRing.maximalIdeal R) q z a horder

/-- A nonzero arbitrary regular function on a finite normalization has
local order at most the principal quotient length of its base norm. -/
theorem finite_dedekind_local_order_le_norm_quotient_length
    (q : Ideal S) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)]
    (z : S) (hz : z ≠ 0) (a : ℕ)
    (horder : algebraMap S (Localization.AtPrime q) z ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a) :
    a ≤ (Module.length R (R ⧸ Ideal.span {Algebra.norm R z})).toNat := by
  exact dvr_power_order_le_quotient_length_toNat (Algebra.norm R z)
    (Algebra.norm_ne_zero_iff.mpr hz) a
    (finite_dedekind_norm_mem_base_maximal_pow q z a horder)

end DimensionFourDependence
