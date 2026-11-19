import DimensionFourDependence.SegreCommonFieldSecondSquares
import DimensionFourDependence.BivariateScalarLinearPowerFactorization
import DimensionFourDependence.TwoRationalRulingPresentations
import DimensionFourDependence.SegreBilinearHyperplaneLift

/-! # The two actual zero-pairing ruling squares give a global hyperplane square -/

namespace DimensionFourDependence

open Polynomial Matrix

universe u
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]

/-- A global scalar-times-bilinear-square factorization is exactly
the original homogeneous hyperplane-square identity after restoring
the radial scale. -/
theorem segre_bilinear_square_constructs_radial_second_hyperplane_identity
    (P B : Polynomial (Polynomial K)) (hB : BivariateBilinear B) (hB0 : B ≠ 0)
    (γ : K) (hγ : γ ≠ 0) (Y : Fin 4 → E) (hY0 : Y 0 ≠ 0)
    (hSegre : Y 0 * Y 3 - Y 1 * Y 2 = 0) (f : E) (d : ℕ)
    (hvalue : f ^ d / Y 0 ^ 2 =
      Polynomial.eval₂ (Polynomial.aeval (Y 2 / Y 0)).toRingHom (Y 1 / Y 0) P)
    (hfactor : P = Polynomial.C (Polynomial.C γ) * B ^ 2) :
    ∃ S : Fin 4 → K, S ≠ 0 ∧
      f ^ d = algebraMap K E γ * (((fun i => algebraMap K E (S i)) ⬝ᵥ Y) ^ 2) := by
  refine ⟨segreBilinearCovector B, segre_bilinear_covector_ne_zero B hB hB0, ?_⟩
  rw [hfactor, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    ← segre_bilinear_polynomial_hyperplane_value B hB Y hY0 hSegre] at hvalue
  simp only [Polynomial.eval₂_C] at hvalue
  have hscalar : (Polynomial.aeval (Y 2 / Y 0)).toRingHom (Polynomial.C γ) = algebraMap K E γ :=
    Polynomial.aeval_C _ γ
  rw [hscalar] at hvalue
  apply (div_left_inj' (pow_ne_zero 2 hY0)).mp
  calc
    _ = _ := hvalue
    _ = _ := by rw [div_pow]; ring

/-- The same original polynomial, with two parameter-algebraic
scalar-linear-square values, constructs an original constant hyperplane.
Exact rational restrictions, descent of both repeated factors, and the
global prime-multiplicity argument are all derived. -/
theorem segre_common_second_square_factorizations_construct_global_radial_hyperplane
    (δ : Fin 3 → Derivation K E E) (Y : Fin 4 → E)
    (hcoord : ∀ i j, δ i (Y j.castSucc) = if j = i then 1 else 0)
    (hY0 : Y 0 ≠ 0) (hSegre : Y 0 * Y 3 - Y 1 * Y 2 = 0)
    (f : E) (hf : f ≠ 0) (d : ℕ) (P : Polynomial (Polynomial K))
    (hPvalue : f ^ d / Y 0 ^ 2 =
      Polynomial.eval₂ (Polynomial.aeval (Y 2 / Y 0)).toRingHom (Y 1 / Y 0) P)
    (hfirst : SegreAlgebraicNormalizedSecondSquareFactorization K Y f d 2)
    (hsecond : SegreAlgebraicNormalizedSecondSquareFactorization K Y f d 1) :
    ∃ (γ : K) (S : Fin 4 → K), γ ≠ 0 ∧ S ≠ 0 ∧
      ((fun i => algebraMap K E (S i)) ⬝ᵥ Y) ≠ 0 ∧
      f ^ d = algebraMap K E γ * (((fun i => algebraMap K E (S i)) ⬝ᵥ Y) ^ 2) := by
  classical
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  letI : NormalizedGCDMonoid K := Classical.arbitrary (NormalizedGCDMonoid K)
  letI : NormalizedGCDMonoid (RatFunc K) := Classical.arbitrary (NormalizedGCDMonoid (RatFunc K))
  obtain ⟨α, a, hα, hαalg, ha, hvalue₁⟩ := hfirst
  obtain ⟨β, b, hβ, hβalg, hb, hvalue₂⟩ := hsecond
  let Z : Fin 3 → E := fun i => Y i.castSucc
  let s := Y 1 / Y 0
  let t := Y 2 / Y 0
  let Ds := segreRatioDerivation δ Z 1
  let Dt := segreRatioDerivation δ Z 2
  have hcast0 : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
  have hcast1 : (1 : Fin 3).castSucc = (1 : Fin 4) := by decide
  have hcast2 : (2 : Fin 3).castSucc = (2 : Fin 4) := by decide
  have hss : Ds s = 1 := by
    simpa only [Ds, s, Z, hcast0, hcast1, ite_true] using
      segreRatioDerivation_ratio δ Z hcoord hY0 1 (by decide) 1
  have hst : Ds t = 0 := by
    simpa only [Ds, t, Z, hcast0, hcast2, show (2 : Fin 3) ≠ 1 from by decide, ite_false] using
      segreRatioDerivation_ratio δ Z hcoord hY0 1 (by decide) 2
  have hts : Dt s = 0 := by
    simpa only [Dt, s, Z, hcast0, hcast1, show (1 : Fin 3) ≠ 2 from by decide, ite_false] using
      segreRatioDerivation_ratio δ Z hcoord hY0 2 (by decide) 1
  have htt : Dt t = 1 := by
    simpa only [Dt, t, Z, hcast0, hcast2, ite_true] using
      segreRatioDerivation_ratio δ Z hcoord hY0 2 (by decide) 2
  have hαa : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (![α, 0] i) := by
    intro i; fin_cases i
    · exact hαalg
    · exact isAlgebraic_zero
  have hβa : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({s} : Set E)) (![β, 0] i) := by
    intro i; fin_cases i
    · exact hβalg
    · exact isAlgebraic_zero
  have hv₁ : f ^ d / Y 0 ^ 2 = (segreRulingPowerPolynomial ![α, 0] a 2).eval s := by
    simpa [segreRulingPowerPolynomial, segreRulingAffineFactor, segreRulingRemainingIndex, s] using hvalue₁
  have hv₂ : f ^ d / Y 0 ^ 2 = (segreRulingPowerPolynomial ![β, 0] b 2).eval t := by
    simpa [segreRulingPowerPolynomial, segreRulingAffineFactor, segreRulingRemainingIndex, t] using hvalue₂
  obtain ⟨φ₁, φ₂, _hφ₁, _hφ₂, he₁, he₂⟩ :=
    two_parameter_algebraic_factored_values_construct_exact_rational_presentations
      Ds Dt s t hss hst hts htt P (f ^ d / Y 0 ^ 2) 2 ![α, 0] a ![β, 0] b
      hαa ha hβa hb hPvalue hv₁ hv₂
  have hP0 : P ≠ 0 := by
    intro hz
    have he := hPvalue
    rw [hz, Polynomial.eval₂_zero] at he
    exact div_ne_zero (pow_ne_zero d hf) (pow_ne_zero 2 hY0) he
  simp only [segreRulingPowerPolynomial, segreRulingAffineFactor, Matrix.cons_val_zero,
    Matrix.cons_val_one, Polynomial.C_0, zero_mul, add_zero] at he₁ he₂
  obtain ⟨γ, B, hγ, hB0, hB, hfactor⟩ :=
    two_extension_scalar_linear_powers_construct_global_bilinear_power
      P hP0 2 (by decide) φ₁.toRingHom φ₂.toRingHom α β hα hβ a b he₁ he₂
  obtain ⟨S, hS, he⟩ := segre_bilinear_square_constructs_radial_second_hyperplane_identity
    P B hB hB0 γ hγ Y hY0 hSegre f d hPvalue hfactor
  refine ⟨γ, S, hγ, hS, ?_, he⟩
  intro hz
  apply pow_ne_zero d hf
  simpa only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero] using he

end DimensionFourDependence
