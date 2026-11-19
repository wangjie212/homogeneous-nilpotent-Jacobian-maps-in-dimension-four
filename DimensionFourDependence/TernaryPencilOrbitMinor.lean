import DimensionFourDependence.ParametricCovectorOrbitMinor
import DimensionFourDependence.TernaryNormalizedParameterJets
import DimensionFourDependence.QuasiTranslationInvariantDivisors
import DimensionFourDependence.ConstantPlaneNormal

/-! # Original normalized pencils construct every nonzero covector orbit minor -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3500000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 3) K
local notation "F₀" => FractionRing (MvPolynomial (Fin 3) K)

/-- The original normalized output support makes the actual
directional pencil numerator nonzero at the same original point. -/
theorem ternary_normalized_source_pencil_direction_numerator_value_ne_zero
    (H : Fin 3 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hcol : ∀ i, aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 0 (H i)) =
      if i = 1 then 1 else 0)
    (p q : R₀) (hp : aeval (Pi.single (0 : Fin 3) (1 : K)) p = 0)
    (hq : aeval (Pi.single (0 : Fin 3) (1 : K)) q = 1)
    (hpartial : aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 1 p) ≠ 0) :
    aeval (Pi.single (0 : Fin 3) (1 : K))
      (q * polynomialVectorDerivation H p - p * polynomialVectorDerivation H q) ≠ 0 := by
  obtain ⟨hsupport, hnonzero⟩ :=
    ternary_normalized_first_jacobian_column_output_support_and_nonzero H hd hH hcol
  have hsum : aeval (Pi.single (0 : Fin 3) (1 : K)) (polynomialVectorDerivation H p) =
      aeval (Pi.single (0 : Fin 3) (1 : K)) (H 1) *
        aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 1 p) := by
    rw [polynomialVectorDerivation_apply, map_sum]
    simp only [map_mul]
    apply Finset.sum_eq_single 1
    · intro i _ hi
      rw [hsupport i hi, zero_mul]
    · simp
  rw [map_sub, map_mul, map_mul, hp, hq, one_mul, zero_mul, sub_zero, hsum]
  exact mul_ne_zero hnonzero hpartial

/-- In the actual source fraction field, the original polynomial
vector field differentiates the original pencil ratio nontrivially.
Neither parameter transcendence nor a derivative condition in a
chosen auxiliary field is assumed. -/
theorem ternary_normalized_source_pencil_ratio_vector_derivation_ne_zero
    (H : Fin 3 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hcol : ∀ i, aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 0 (H i)) =
      if i = 1 then 1 else 0)
    (p q : R₀) (hp : aeval (Pi.single (0 : Fin 3) (1 : K)) p = 0)
    (hq : aeval (Pi.single (0 : Fin 3) (1 : K)) q = 1)
    (hpartial : aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 1 p) ≠ 0) :
    sourceVectorDerivation (fun i => algebraMap R₀ F₀ (H i))
      (algebraMap R₀ F₀ p / algebraMap R₀ F₀ q) ≠ 0 := by
  let φ := algebraMap R₀ F₀
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hq
    exact zero_ne_one hq
  have hqF : φ q ≠ 0 := fun hz => hq0 (IsFractionRing.injective R₀ F₀ (hz.trans (map_zero _).symm))
  have hn : q * polynomialVectorDerivation H p - p * polynomialVectorDerivation H q ≠ 0 := by
    intro hz
    have he := ternary_normalized_source_pencil_direction_numerator_value_ne_zero H hd hH hcol p q hp hq hpartial
    exact he (by rw [hz, map_zero])
  have hnF : φ (q * polynomialVectorDerivation H p - p * polynomialVectorDerivation H q) ≠ 0 :=
    fun hz => hn (IsFractionRing.injective R₀ F₀ (hz.trans (map_zero _).symm))
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul, sourceVectorDerivation_polynomialVectorDerivation]
  change (φ q)⁻¹ ^ 2 * (φ q * φ (polynomialVectorDerivation H p) -
    φ p * φ (polynomialVectorDerivation H q)) ≠ 0
  exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hqF))
    (by simpa only [map_sub, map_mul] using hnF)

/-- The original normalized polynomial pencil and component
independence make every constant covector-pair minor on the output
and its actual Jacobian acceleration a nonzero source polynomial. -/
theorem ternary_normalized_independent_source_pencil_covector_orbit_minor_ne_zero
    (H : Fin 3 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H)
    (hcol : ∀ i, aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 0 (H i)) =
      if i = 1 then 1 else 0)
    (p q g : R₀) (hg : g ≠ 0)
    (hp : aeval (Pi.single (0 : Fin 3) (1 : K)) p = 0)
    (hq : aeval (Pi.single (0 : Fin 3) (1 : K)) q = 1)
    (hpartial : aeval (Pi.single (0 : Fin 3) (1 : K)) (pderiv 1 p) ≠ 0)
    (v : Fin 3 → Polynomial K) {N : ℕ} (hN : ∀ i, (v i).natDegree ≤ N)
    (hfactor : ∀ i, H i = g * homogeneousParameterPolynomialValue (v i) N p q)
    (μ ν : Fin 3 → K) (hμν : LinearIndependent K ![μ, ν]) :
    outputLinearCombination H μ * outputLinearCombination (jac H *ᵥ H) ν -
      outputLinearCombination H ν * outputLinearCombination (jac H *ᵥ H) μ ≠ 0 := by
  let φ : R₀ →ₐ[K] F₀ := IsScalarTower.toAlgHom K R₀ F₀
  let Y : Fin 3 → F₀ := fun i => φ (H i)
  let D := sourceVectorDerivation Y
  let t := φ p / φ q
  let s := φ g * φ q ^ N
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hq
    exact zero_ne_one hq
  have hqF : φ q ≠ 0 := fun hz => hq0 (IsFractionRing.injective R₀ F₀ (hz.trans (map_zero _).symm))
  have hgF : φ g ≠ 0 := fun hz => hg (IsFractionRing.injective R₀ F₀ (hz.trans (map_zero _).symm))
  have hs : s ≠ 0 := mul_ne_zero hgF (pow_ne_zero N hqF)
  have ht : D t ≠ 0 := ternary_normalized_source_pencil_ratio_vector_derivation_ne_zero
    H hd hH hcol p q hp hq hpartial
  have hrep (i) : Y i = s * Polynomial.aeval t (v i) := by
    change φ (H i) = _
    rw [hfactor i, map_mul, homogeneousParameterPolynomialValue_algHom,
      homogeneousParameterPolynomialValue_fraction (v i) (hN i) _ _ hqF]
    simp only [s, t, mul_assoc]
  have hY : LinearIndependent K Y := (linearIndependent_of_componentsIndependent H hind).map'
    φ.toLinearMap (LinearMap.ker_eq_bot.mpr (IsFractionRing.injective R₀ F₀))
  have hminor := independent_covectors_scaled_parameter_orbit_minor_ne_zero
    D Y hY s t hs ht v hrep μ ν hμν
  have hacc (i) : D (Y i) = φ ((jac H *ᵥ H) i) := by
    rw [show D (Y i) = φ (polynomialVectorDerivation H (H i)) from
      sourceVectorDerivation_polynomialVectorDerivation H (H i)]
    congr 1
    simp only [polynomialVectorDerivation_apply, Matrix.mulVec, dotProduct, jac, Matrix.of_apply, mul_comm]
  have hC (c : K) : φ (C c) = algebraMap K F₀ c := φ.commutes c
  have hsum (c : Fin 3 → K) : φ (outputLinearCombination H c) = ∑ i, c i • Y i := by
    simp only [outputLinearCombination, map_sum, map_mul, hC, Algebra.smul_def]
    rfl
  have hsumacc (c : Fin 3 → K) :
      φ (outputLinearCombination (jac H *ᵥ H) c) = ∑ i, c i • D (Y i) := by
    simp only [outputLinearCombination, map_sum, map_mul, hC, Algebra.smul_def, hacc]
  intro hz
  apply hminor
  simpa only [map_sub, map_mul, map_zero, hsum, hsumacc] using congrArg φ hz

end DimensionFourDependence
