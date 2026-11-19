import DimensionFourDependence.ClosedParameterVectorDescent
import DimensionFourDependence.SegreNormalizedRulingPolynomial

/-! # Both actual finite ruling factors are realized in the original closed geometric field -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 2500000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- The actual normalized ruling value retains a full linear-times-
power presentation in the common geometric field, with every factor
coefficient algebraic over the specified original parameter alone. -/
def SegreAlgebraicNormalizedRulingFactorization
    (K : Type u) [Field K] [Algebra K E] (Y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3) : Prop :=
  ∃ A B : Fin 2 → E,
    (∀ i, IsAlgebraic (IntermediateField.adjoin K ({Y j.castSucc / Y 0} : Set E)) (A i)) ∧
    (∀ i, IsAlgebraic (IntermediateField.adjoin K ({Y j.castSucc / Y 0} : Set E)) (B i)) ∧
    f ^ d / Y 0 ^ (d + 1) = (segreRulingPowerPolynomial A B d).eval
      (Y (segreRulingRemainingIndex j).castSucc / Y 0)

/-- The original finite boundary factorization constructs both actual
geometric covectors, retaining their separate smaller parameter
algebraicity and exact normalized value. No common-field factor
presentation or descent assumption is supplied. -/
theorem finite_segre_ruling_factors_descend_to_common_geometric_constants
    [IsAlgClosed E] (Y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3)
    (hj : j ≠ 0) (hY0 : Y 0 ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hfactor : SegreFiniteRadialProductFactorization K Y f d j p) :
    SegreAlgebraicNormalizedRulingFactorization K Y f d j := by
  obtain ⟨a, _ha, C, hC, R, B, _hR, _hB, hpower, _hroot, _hRY, _hBY⟩ := hfactor
  let κ := projectivePrimeRatioField p (some a)
  let J := segreProjectiveRulingParameterField K Y j p a
  let tJ : J := ⟨algebraMap E κ (Y j.castSucc / Y 0),
    IntermediateField.subset_adjoin K _ (by rfl)⟩
  let t : C := algebraMap J C tJ
  have ht : algebraMap C κ t = algebraMap E κ (Y j.castSucc / Y 0) := rfl
  let Z : Fin 3 → κ := fun i => algebraMap E κ (Y i.castSucc)
  have hcast0 : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
  have hZ0 : Z 0 ≠ 0 := (map_ne_zero (algebraMap E κ)).mpr hY0
  have hrel : Z j = algebraMap C κ t * Z 0 := by
    rw [ht]
    change algebraMap E κ (Y j.castSucc) = algebraMap E κ (Y j.castSucc / Y 0) * algebraMap E κ (Y 0)
    rw [map_div₀]
    exact (div_mul_cancel₀ _ hZ0).symm
  have hvalueκ : (algebraMap E κ f) ^ d / Z 0 ^ (d + 1) =
      Polynomial.aeval (Z (segreRulingRemainingIndex j) / Z 0)
        (segreRulingPowerPolynomial (segreRulingBinaryCoefficients j t R)
          (segreRulingBinaryCoefficients j t B) d) := by
    rw [hpower]
    exact segre_ruling_factored_pairing_normalized_polynomial_value j hj t R B Z hZ0 hrel d
  have hvalue : algebraMap E κ (f ^ d / Y 0 ^ (d + 1)) =
      Polynomial.aeval (algebraMap E κ (Y (segreRulingRemainingIndex j).castSucc / Y 0))
        (segreRulingPowerPolynomial (segreRulingBinaryCoefficients j t R)
          (segreRulingBinaryCoefficients j t B) d) := by
    simpa only [Z, hcast0, map_div₀, map_pow] using hvalueκ
  obtain ⟨A, D, _hAmap, _hDmap, hAalg, hDalg, he⟩ :=
    finite_parameter_linear_power_value_descends_to_closed_constants
      (Y j.castSucc / Y 0) (Y (segreRulingRemainingIndex j).castSucc / Y 0)
      (f ^ d / Y 0 ^ (d + 1)) C hC
      (segreRulingBinaryCoefficients j t R) (segreRulingBinaryCoefficients j t B) d hvalue
  exact ⟨A, D, hAalg, hDalg, he⟩

end DimensionFourDependence
