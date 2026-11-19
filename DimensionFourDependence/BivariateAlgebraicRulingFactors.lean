import DimensionFourDependence.BivariateRulingPowerFactorization

/-! # Ruling factors over arbitrary extensions construct the original global factorization -/

namespace DimensionFourDependence

open Polynomial

set_option maxHeartbeats 3000000

variable {K F E₁ E₂ : Type*} [Field K] [NormalizedGCDMonoid K]
    [Field F] [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F]
    [NormalizationMonoid F] [Field E₁] [CharZero E₁] [Field E₂] [CharZero E₂]
    [DecidableEq (Polynomial (Polynomial K))] [DecidableEq (Polynomial F)]

/-- Separate extension-field ruling factorizations descend and
construct an exact global original-constant bilinear factorization.
Neither the factors' descent nor a global divisor decomposition is assumed. -/
theorem two_extension_ruling_presentations_construct_global_bilinear_power_factorization
    (P : Polynomial (Polynomial K)) (hP : P ≠ 0) (d : ℕ) (hd : 1 < d)
    (f₁ : F →+* E₁) (f₂ : F →+* E₂)
    (a₁ b₁ : Fin 2 → E₁) (a₂ b₂ : Fin 2 → E₂)
    (hfirst : (P.map (algebraMap (Polynomial K) F)).map f₁ = segreRulingPowerPolynomial a₁ b₁ d)
    (hsecond : ((Polynomial.Bivariate.swap P).map (algebraMap (Polynomial K) F)).map f₂ =
      segreRulingPowerPolynomial a₂ b₂ d) :
    ∃ R B : Polynomial (Polynomial K), R ≠ 0 ∧ B ≠ 0 ∧
      BivariateBilinear R ∧ BivariateBilinear B ∧ P = R * B ^ d := by
  classical
  have hinj := Polynomial.map_injective (algebraMap (Polynomial K) F)
    (IsFractionRing.injective (Polynomial K) F)
  have hmap0 (Q : Polynomial (Polynomial K)) (hQ : Q ≠ 0) :
      Q.map (algebraMap (Polynomial K) F) ≠ 0 := by
    intro h
    apply hQ
    apply hinj
    simpa only [Polynomial.map_zero] using h
  have hswap0 : Polynomial.Bivariate.swap P ≠ 0 := by
    intro h
    apply hP
    apply Polynomial.Bivariate.swap.injective
    simpa only [map_zero] using h
  obtain ⟨A, B, hA, hB, hdegA, hdegB, he₁⟩ :=
    univariate_linear_times_power_constructs_original_linear_factors f₁ _ (hmap0 P hP)
      a₁ b₁ d hd hfirst
  obtain ⟨C, D, hC, hD, hdegC, hdegD, he₂⟩ :=
    univariate_linear_times_power_constructs_original_linear_factors f₂ _ (hmap0 _ hswap0)
      a₂ b₂ d hd hsecond
  exact two_fraction_ruling_presentations_construct_global_bilinear_power_factorization
    P hP d hd A B C D hA hB hC hD hdegA hdegB hdegC hdegD he₁ he₂

end DimensionFourDependence
