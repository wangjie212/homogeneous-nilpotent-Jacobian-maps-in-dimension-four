import DimensionFourDependence.SegreRulingBinaryPolynomial

/-! # The original scale-free radial pairing is a bounded polynomial along each ruling -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [Field E] [Algebra K E]

/-- The original radial-scale-free function is a polynomial of degree
at most d+1 in the original varying ruling ratio, over one finite
extension of the specified original ruling parameter field. -/
def SegreBoundedNormalizedRulingPolynomial
    (K : Type u) [Field K] [Algebra K E] (Y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E)) : Prop :=
  ∃ a : Fin 4, X (some a) ∉ p.asHomogeneousIdeal ∧
    ∃ C : IntermediateField (segreProjectiveRulingParameterField K Y j p a)
        (projectivePrimeRatioField p (some a)),
      Module.Finite (segreProjectiveRulingParameterField K Y j p a) C ∧
      ∃ P : Polynomial C, P ≠ 0 ∧ P.natDegree ≤ d + 1 ∧
        (algebraMap E (projectivePrimeRatioField p (some a)) f) ^ d /
            (algebraMap E (projectivePrimeRatioField p (some a)) (Y 0)) ^ (d + 1) =
          Polynomial.aeval
            (algebraMap E (projectivePrimeRatioField p (some a)) (Y (segreRulingRemainingIndex j).castSucc) /
              algebraMap E (projectivePrimeRatioField p (some a)) (Y 0)) P

/-- The actual finite ruling factorization constructs the exact
bounded polynomial description of the original normalized pairing.
The coefficient field, its parameter value and the varying coordinate
ratio are retained in the same actual normalized coordinate field. -/
theorem finite_segre_radial_product_factorization_constructs_normalized_polynomial
    (Y : Fin 4 → E) (f : E) (d : ℕ) (j : Fin 3) (hj : j ≠ 0) (hY0 : Y 0 ≠ 0)
    (p : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hfactor : SegreFiniteRadialProductFactorization K Y f d j p) :
    SegreBoundedNormalizedRulingPolynomial K Y f d j p := by
  obtain ⟨a, ha, C, hC, R, B, _hR, _hB, hpower, _hroot, hRY, hBY⟩ := hfactor
  let κ := projectivePrimeRatioField p (some a)
  let J := segreProjectiveRulingParameterField K Y j p a
  let tJ : J := ⟨algebraMap E κ (Y j.castSucc / Y 0),
    IntermediateField.subset_adjoin K _ (by rfl)⟩
  let t : C := algebraMap J C tJ
  have ht : algebraMap C κ t = algebraMap E κ (Y j.castSucc / Y 0) := rfl
  let Z : Fin 3 → κ := fun i => algebraMap E κ (Y i.castSucc)
  have hZ0 : Z 0 ≠ 0 := (map_ne_zero (algebraMap E κ)).mpr hY0
  have hrel : Z j = algebraMap C κ t * Z 0 := by
    rw [ht]
    change algebraMap E κ (Y j.castSucc) = algebraMap E κ (Y j.castSucc / Y 0) * algebraMap E κ (Y 0)
    rw [map_div₀]
    exact (div_mul_cancel₀ _ hZ0).symm
  let P := segreRulingPowerPolynomial (segreRulingBinaryCoefficients j t R) (segreRulingBinaryCoefficients j t B) d
  have hvalue : (algebraMap E κ f) ^ d / Z 0 ^ (d + 1) =
      Polynomial.aeval (Z (segreRulingRemainingIndex j) / Z 0) P := by
    rw [hpower]
    exact segre_ruling_factored_pairing_normalized_polynomial_value j hj t R B Z hZ0 hrel d
  have hpower0 : (algebraMap E κ f) ^ d ≠ 0 := by
    rw [hpower]
    exact mul_ne_zero hRY (pow_ne_zero d hBY)
  have hP : P ≠ 0 := by
    intro he
    rw [he, map_zero] at hvalue
    exact (div_ne_zero hpower0 (pow_ne_zero (d + 1) hZ0)) hvalue
  exact ⟨a, ha, C, hC, P, hP, segreRulingPowerPolynomial_natDegree_le _ _ _, hvalue⟩

end DimensionFourDependence
