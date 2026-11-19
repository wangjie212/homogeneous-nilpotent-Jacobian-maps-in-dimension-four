import DimensionFourDependence.ScalarLinearPowerCanonicalFactors
import DimensionFourDependence.BivariateBilinearCoefficients

/-! # Two scalar linear powers give one original global bilinear power -/

namespace DimensionFourDependence

open Polynomial

set_option maxHeartbeats 3500000

variable {K F : Type*} [Field K] [NormalizedGCDMonoid K]
    [Field F] [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F]
    [NormalizationMonoid F]
    [DecidableEq (Polynomial (Polynomial K))] [DecidableEq (Polynomial F)]

/-- A polynomial constant in each of its two original variables is
exactly its original scalar constant. -/
theorem bivariate_eq_original_constant_of_both_natDegree_zero
    (P : Polynomial (Polynomial K)) (hP : P.natDegree = 0)
    (hswap : (Polynomial.Bivariate.swap P).natDegree = 0) :
    P = Polynomial.C (Polynomial.C ((P.coeff 0).coeff 0)) := by
  have houter : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hP
  have hinner : P.coeff 0 = Polynomial.C ((P.coeff 0).coeff 0) := by
    ext n
    by_cases hn : n = 0
    · subst n; simp
    · rw [Polynomial.coeff_C, if_neg hn, ← bivariate_swap_coeff_coeff P n 0]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega :
        (Polynomial.Bivariate.swap P).natDegree < n)]
      simp
  exact houter.trans (congrArg Polynomial.C hinner)

/-- Two exact rational ruling presentations as scalar times a pure
linear power force one original global scalar and one bilinear factor.
Prime-exponent remainders and their behavior under localization supply
the global compatibility; no global square or divisor decomposition is assumed. -/
theorem two_fraction_scalar_linear_powers_construct_global_bilinear_power
    (P : Polynomial (Polynomial K)) (hP : P ≠ 0) (d : ℕ) (hd : 0 < d)
    (α β : F) (hα : α ≠ 0) (hβ : β ≠ 0)
    (A B : Polynomial F) (hA : A ≠ 0) (hB : B ≠ 0)
    (hdegA : A.natDegree ≤ 1) (hdegB : B.natDegree ≤ 1)
    (hfirst : P.map (algebraMap (Polynomial K) F) = Polynomial.C α * A ^ d)
    (hsecond : (Polynomial.Bivariate.swap P).map (algebraMap (Polynomial K) F) =
      Polynomial.C β * B ^ d) :
    ∃ (γ : K) (D : Polynomial (Polynomial K)), γ ≠ 0 ∧ D ≠ 0 ∧
      BivariateBilinear D ∧ P = Polynomial.C (Polynomial.C γ) * D ^ d := by
  classical
  have hswap0 : Polynomial.Bivariate.swap P ≠ 0 := by
    intro hz
    apply hP
    apply Polynomial.Bivariate.swap.injective
    simpa only [map_zero] using hz
  obtain ⟨hr1, hq1⟩ := fraction_scalar_linear_power_original_canonical_degree_bounds
    P hP α hα A hA hdegA d hd hfirst
  obtain ⟨hr2, hq2⟩ := fraction_scalar_linear_power_original_canonical_degree_bounds
    _ hswap0 β hβ B hB hdegB d hd hsecond
  obtain ⟨hrswap, hqswap⟩ := ring_equiv_canonical_power_factors_associated
    (Polynomial.Bivariate.swap (R := K)).toRingEquiv P hP d hd
  have hrdeg := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hrswap)
  have hqdeg := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hqswap)
  have hRswap : (Polynomial.Bivariate.swap (factorizationPowerRemainder P d)).natDegree = 0 :=
    hrdeg.symm.trans hr2
  have hQ : BivariateBilinear (factorizationPowerQuotient P d) :=
    ⟨hq1, hqdeg.symm.le.trans hq2⟩
  obtain ⟨u, hu⟩ := factorization_power_remainder_quotient_exact P hP d
  let R := (u : Polynomial (Polynomial K)) * factorizationPowerRemainder P d
  have hRdegree : R.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact Polynomial.natDegree_mul_le.trans (by
      rw [Polynomial.natDegree_eq_zero_of_isUnit (Units.isUnit u), hr1])
  have hRswapdegree : (Polynomial.Bivariate.swap R).natDegree = 0 := by
    change (Polynomial.Bivariate.swap ((u : Polynomial (Polynomial K)) * _)).natDegree = 0
    rw [map_mul]
    apply Nat.eq_zero_of_le_zero
    have huswap := (Units.isUnit u).map (Polynomial.Bivariate.swap (R := K)).toRingHom
    change IsUnit (Polynomial.Bivariate.swap (u : Polynomial (Polynomial K))) at huswap
    exact Polynomial.natDegree_mul_le.trans (by
      rw [Polynomial.natDegree_eq_zero_of_isUnit huswap, hRswap])
  have hRconstant := bivariate_eq_original_constant_of_both_natDegree_zero R hRdegree hRswapdegree
  have hR0 : R ≠ 0 := mul_ne_zero (Units.ne_zero u)
    (factorization_support_power_product_ne_zero P (fun p => factorization P p % d))
  have hγ : (R.coeff 0).coeff 0 ≠ 0 := by
    intro hz
    apply hR0
    rw [hRconstant, hz, Polynomial.C_0, Polynomial.C_0]
  refine ⟨(R.coeff 0).coeff 0, factorizationPowerQuotient P d, hγ,
    factorization_support_power_product_ne_zero P (fun p => factorization P p / d), hQ, ?_⟩
  exact hu.trans (congrArg (fun A => A * factorizationPowerQuotient P d ^ d) hRconstant)

variable {E₁ E₂ : Type*} [Field E₁] [CharZero E₁] [Field E₂] [CharZero E₂]

/-- Separate extension fields for the two rulings give the same
original scalar-times-bilinear-power identity. -/
theorem two_extension_scalar_linear_powers_construct_global_bilinear_power
    (P : Polynomial (Polynomial K)) (hP : P ≠ 0) (d : ℕ) (hd : 0 < d)
    (f₁ : F →+* E₁) (f₂ : F →+* E₂) (α : E₁) (β : E₂)
    (hα : α ≠ 0) (hβ : β ≠ 0) (a : Fin 2 → E₁) (b : Fin 2 → E₂)
    (hfirst : (P.map (algebraMap (Polynomial K) F)).map f₁ =
      Polynomial.C α * segreRulingAffineFactor a ^ d)
    (hsecond : ((Polynomial.Bivariate.swap P).map (algebraMap (Polynomial K) F)).map f₂ =
      Polynomial.C β * segreRulingAffineFactor b ^ d) :
    ∃ (γ : K) (D : Polynomial (Polynomial K)), γ ≠ 0 ∧ D ≠ 0 ∧
      BivariateBilinear D ∧ P = Polynomial.C (Polynomial.C γ) * D ^ d := by
  classical
  have hmap0 (Q : Polynomial (Polynomial K)) (hQ : Q ≠ 0) :
      Q.map (algebraMap (Polynomial K) F) ≠ 0 := by
    intro hz
    apply hQ
    apply Polynomial.map_injective _ (IsFractionRing.injective (Polynomial K) F)
    simpa only [Polynomial.map_zero] using hz
  have hswap0 : Polynomial.Bivariate.swap P ≠ 0 := by
    intro hz
    apply hP
    apply Polynomial.Bivariate.swap.injective
    simpa only [map_zero] using hz
  obtain ⟨α₀, A, hα₀, hA, hdegA, he₁⟩ := univariate_scalar_linear_power_factorization_descends
    f₁ _ (hmap0 P hP) a α hα d hd hfirst
  obtain ⟨β₀, B, hβ₀, hB, hdegB, he₂⟩ := univariate_scalar_linear_power_factorization_descends
    f₂ _ (hmap0 _ hswap0) b β hβ d hd hsecond
  exact two_fraction_scalar_linear_powers_construct_global_bilinear_power
    P hP d hd α₀ β₀ hα₀ hβ₀ A B hA hB hdegA hdegB he₁ he₂

end DimensionFourDependence
