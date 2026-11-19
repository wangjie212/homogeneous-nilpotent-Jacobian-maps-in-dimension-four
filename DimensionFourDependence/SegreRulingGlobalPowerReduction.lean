import DimensionFourDependence.SegreBilinearHyperplaneLift
import DimensionFourDependence.Nilpotent

/-! # From the two rational ruling presentations to the original radial hyperplane identity -/

namespace DimensionFourDependence

open Polynomial Matrix

set_option maxHeartbeats 3000000

/-- The strict degree condition in the power-factor argument follows
from the original homogeneous nilpotent and independence hypotheses. -/
theorem independent_nilpotent_homogeneous_degree_greater_than_one
    {K : Type*} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H) :
    1 < d := by
  by_contra h
  have hd1 : d = 1 := by omega
  subst d
  exact hind (dependence_degree_one H hH hN)

/-- The original bivariate value identity and two exact ruling
presentations over extensions of the original rational parameter field
construct (5.3). Normalization choices, descent, prime multiplicities,
global divisor decomposition and constant covectors are all constructed
internally. The separate remaining task is to derive these two polynomial
presentations from the selected original boundary points. -/
theorem segre_two_extension_ruling_identities_construct_original_radial_hyperplanes
    {K E F E₁ E₂ : Type*} [Field K] [Field E] [Algebra K E]
    [Field F] [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F]
    [Field E₁] [CharZero E₁] [Field E₂] [CharZero E₂]
    (P : Polynomial (Polynomial K)) (Y : Fin 4 → E) (hY0 : Y 0 ≠ 0)
    (hSegre : Y 0 * Y 3 - Y 1 * Y 2 = 0) (f : E) (hf : f ≠ 0)
    (d : ℕ) (hd : 1 < d)
    (hvalue : f ^ d / Y 0 ^ (d + 1) =
      Polynomial.eval₂ (Polynomial.aeval (Y 2 / Y 0)).toRingHom (Y 1 / Y 0) P)
    (f₁ : F →+* E₁) (f₂ : F →+* E₂)
    (a₁ b₁ : Fin 2 → E₁) (a₂ b₂ : Fin 2 → E₂)
    (hfirst : (P.map (algebraMap (Polynomial K) F)).map f₁ = segreRulingPowerPolynomial a₁ b₁ d)
    (hsecond : ((Polynomial.Bivariate.swap P).map (algebraMap (Polynomial K) F)).map f₂ =
      segreRulingPowerPolynomial a₂ b₂ d) :
    ∃ r b : Fin 4 → K, r ≠ 0 ∧ b ≠ 0 ∧
      ((fun i => algebraMap K E (r i)) ⬝ᵥ Y) ≠ 0 ∧
      ((fun i => algebraMap K E (b i)) ⬝ᵥ Y) ≠ 0 ∧
      f ^ d = ((fun i => algebraMap K E (r i)) ⬝ᵥ Y) *
        ((fun i => algebraMap K E (b i)) ⬝ᵥ Y) ^ d := by
  classical
  letI : NormalizedGCDMonoid K := Classical.arbitrary (NormalizedGCDMonoid K)
  letI : NormalizedGCDMonoid F := Classical.arbitrary (NormalizedGCDMonoid F)
  have hP0 : P ≠ 0 := by
    intro h
    have hz : f ^ d / Y 0 ^ (d + 1) = 0 := by simpa only [h, Polynomial.eval₂_zero] using hvalue
    exact div_ne_zero (pow_ne_zero _ hf) (pow_ne_zero _ hY0) hz
  obtain ⟨R, B, hR0, hB0, hR, hB, hfactor⟩ :=
    two_extension_ruling_presentations_construct_global_bilinear_power_factorization
      P hP0 d hd f₁ f₂ a₁ b₁ a₂ b₂ hfirst hsecond
  obtain ⟨r, b, hr, hb, he⟩ := segre_bilinear_power_factorization_constructs_radial_hyperplane_identity
    P R B hR hB hR0 hB0 Y hY0 hSegre f d hvalue hfactor
  refine ⟨r, b, hr, hb, ?_, ?_, he⟩
  · intro h
    exact pow_ne_zero d hf (by simpa only [h, zero_mul] using he)
  · intro h
    exact pow_ne_zero d hf (by simpa only [h, zero_pow (by omega : d ≠ 0), mul_zero] using he)

end DimensionFourDependence
