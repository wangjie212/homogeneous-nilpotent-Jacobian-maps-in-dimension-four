import DimensionFourDependence.ZeroAccelerationPolynomialTranslation
import DimensionFourDependence.InvariantVectorTraceConstraints
import DimensionFourDependence.ProjectiveSourceParameterField

/-! # Nonzero quasi-translation invariants have invariant polynomial divisors

The proof uses the actual finite polynomial line identity. A product
restricting to a nonzero constant has constant factors in the parameter;
the coefficient derivation then annihilates both original factor values.
This supplies the invariant-divisor step in de Bondt's Theorem 5.3.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2500000

variable {K F : Type*} [Field K] [Field F] [CharZero F] [Algebra K F] {n : ℕ}

/-- With zero coordinate acceleration, a nonzero invariant product
forces both polynomial factor values to be invariant. -/
theorem zero_acceleration_derivation_invariant_product_factors
    (D : Derivation K F F) (y : Fin n → F)
    (hacc : ∀ i, D (D (y i)) = 0) (p q : MvPolynomial (Fin n) K)
    (hpq0 : aeval y (p * q) ≠ 0) (hpq : D (aeval y (p * q)) = 0) :
    D (aeval y p) = 0 ∧ D (aeval y q) = 0 := by
  let L : MvPolynomial (Fin n) K → Polynomial F :=
    affineLinePolynomialRestriction y (fun i => D (y i))
  have hprod : L p * L q = Polynomial.C (aeval y (p * q)) := by
    simpa only [L, affineLinePolynomialRestriction, map_mul] using
      invariant_polynomial_constant_on_zero_acceleration_line D y hacc (p * q) hpq
  have hunit : IsUnit (L p * L q) := by
    rw [hprod]
    exact (isUnit_iff_ne_zero.mpr hpq0).map Polynomial.C
  have hunits : IsUnit (L p) ∧ IsUnit (L q) := (Commute.all _ _).isUnit_mul_iff.mp hunit
  have hfactor (r : MvPolynomial (Fin n) K) (hr : IsUnit (L r)) : D (aeval y r) = 0 := by
    have hcoef : (L r).coeff 0 = aeval y r := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simpa only [mul_zero, add_zero] using
        affineLinePolynomialRestriction_eval y (fun i => D (y i)) 0 r
    have hconst : L r = Polynomial.C (aeval y r) :=
      (Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hr)).trans
        (congrArg Polynomial.C hcoef)
    have he := aeval_line_coefficient_derivation D y (fun i => D (y i)) (fun _ => rfl) hacc r
    change polynomialCoefficientDerivation D (L r) = (L r).derivative at he
    rw [hconst, polynomialCoefficientDerivation_C, Polynomial.derivative_C] at he
    simpa only [Polynomial.coeff_C_zero, Polynomial.coeff_zero] using
      congrArg (fun P : Polynomial F => P.coeff 0) he
  exact ⟨hfactor p hunits.1, hfactor q hunits.2⟩

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "P₀" => MvPolynomial (Fin n) K
local notation "F₀" => FractionRing (MvPolynomial (Fin n) K)

/-- The original polynomial derivation agrees exactly with the
source-field derivation on every original polynomial. -/
theorem sourceVectorDerivation_polynomialVectorDerivation
    (u : Fin n → P₀) (p : P₀) :
    sourceVectorDerivation (fun i => algebraMap P₀ F₀ (u i)) (algebraMap P₀ F₀ p) =
      algebraMap P₀ F₀ (polynomialVectorDerivation u p) := by
  simp only [sourceVectorDerivation_apply, rationalPartial_polynomial,
    polynomialVectorDerivation_apply, map_sum, map_mul]

/-- The actual polynomial invariants of a zero-acceleration direction
are factorially closed in the original polynomial source. -/
theorem zero_acceleration_polynomial_derivation_factorially_closed
    (u : Fin n → P₀) (hacc : jac u *ᵥ u = 0) (p q : P₀)
    (hpq0 : p * q ≠ 0) (hpq : polynomialVectorDerivation u (p * q) = 0) :
    polynomialVectorDerivation u p = 0 ∧ polynomialVectorDerivation u q = 0 := by
  let U : Fin n → F₀ := fun i => algebraMap P₀ F₀ (u i)
  let D := sourceVectorDerivation U
  have haccF (i : Fin n) : D (D (rationalCoordinate (K := K) i)) = 0 := by
    rw [sourceVectorDerivation_coordinate]
    change sourceVectorDerivation U (algebraMap P₀ F₀ (u i)) = 0
    rw [sourceVectorDerivation_polynomialVectorDerivation,
      polynomialVectorDerivation_output_zero_of_kernel u u hacc i, map_zero]
  have hnonzero : aeval (rationalCoordinate (K := K)) (p * q) ≠ 0 := by
    rw [rationalCoordinate_aeval]
    exact fun hz => hpq0 (IsFractionRing.injective P₀ F₀ (hz.trans (map_zero _).symm))
  have hproduct : D (aeval (rationalCoordinate (K := K)) (p * q)) = 0 := by
    rw [rationalCoordinate_aeval, sourceVectorDerivation_polynomialVectorDerivation, hpq, map_zero]
  obtain ⟨hp, hq⟩ := zero_acceleration_derivation_invariant_product_factors D
    (rationalCoordinate (K := K)) haccF p q hnonzero hproduct
  have hreflect (r : P₀) (hr : D (aeval (rationalCoordinate (K := K)) r) = 0) :
      polynomialVectorDerivation u r = 0 := by
    rw [rationalCoordinate_aeval, sourceVectorDerivation_polynomialVectorDerivation] at hr
    exact IsFractionRing.injective P₀ F₀ (hr.trans (map_zero _).symm)
  exact ⟨hreflect p hp, hreflect q hq⟩

/-- Every polynomial divisor of a nonzero actual invariant is itself
annihilated by the original directional derivation. -/
theorem zero_acceleration_polynomial_invariant_divisor_is_invariant
    (u : Fin n → P₀) (hacc : jac u *ᵥ u = 0) (f : P₀) (hf0 : f ≠ 0)
    (hf : polynomialVectorDerivation u f = 0) (p : P₀) (hpf : p ∣ f) :
    polynomialVectorDerivation u p = 0 := by
  obtain ⟨q, hq⟩ := hpf
  exact (zero_acceleration_polynomial_derivation_factorially_closed u hacc p q
    (by rwa [← hq]) (by rwa [← hq])).1

/-- Divisors of an original nonzero invariant are fixed by each actual
polynomial translation, supplying both the differential and substitution
forms of the invariant-divisor assertion used in classification. -/
theorem zero_acceleration_polynomial_translation_preserves_invariant_divisor
    (u : Fin 4 → MvPolynomial (Fin 4) K) (hacc : jac u *ᵥ u = 0)
    (f : MvPolynomial (Fin 4) K) (hf0 : f ≠ 0) (hf : polynomialVectorDerivation u f = 0)
    (p : MvPolynomial (Fin 4) K) (hpf : p ∣ f) (s : K) :
    polynomialDirectionTranslation u s p = p := by
  have hp := zero_acceleration_polynomial_invariant_divisor_is_invariant u hacc f hf0 hf p hpf
  have hker : jac (fun _ : Fin 4 => p) *ᵥ u = 0 := by
    funext i
    simpa only [Matrix.mulVec, dotProduct, jac, Matrix.of_apply,
      polynomialVectorDerivation_apply, Pi.zero_apply, mul_comm] using hp
  exact zero_acceleration_polynomial_translation_preserves_kernel_map u hacc
    (fun _ : Fin 4 => p) hker s 0

end DimensionFourDependence
