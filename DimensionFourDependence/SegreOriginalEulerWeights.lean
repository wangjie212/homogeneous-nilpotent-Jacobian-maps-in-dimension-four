import DimensionFourDependence.SegreOriginalSourceChart
import DimensionFourDependence.SourceEuler
import DimensionFourDependence.PrimitiveMapDegree

/-! # The original source Euler operator constructs the Segre row and slope weights -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]

local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "X₀" => rationalCoordinate (K := K) (n := 4)
local notation "E₀" => sourceEuler (K := K) (n := 4)
local notation "D₀" => segreOriginalSourceChartDerivation (K := K)
local notation "t₀" => segreOriginalSourceRulingParameter (K := K)
local notation "π₀" => segreOriginalSourceUniformizer (K := K)

/-- The original ruling parameter has source Euler weight zero. -/
theorem segre_original_source_parameter_euler_zero : (E₀) (t₀) = 0 := by
  rw [segreOriginalSourceRulingParameter, Derivation.leibniz_div]
  simp only [sourceEuler_coordinate, smul_eq_mul]
  ring

/-- The determinant divided by the first source coordinate has weight
one, retaining the actual source uniformizer rather than its square. -/
theorem segre_original_source_uniformizer_euler : (E₀) (π₀) = (π₀) := by
  rw [segreOriginalSourceUniformizer, map_sub, Derivation.leibniz,
    segre_original_source_parameter_euler_zero, sourceEuler_coordinate, sourceEuler_coordinate]
  simp [smul_eq_mul, segreOriginalSourceUniformizer]

/-- Euler scaling in the exact original chart has no ruling-parameter
component. Its transverse term is the given source uniformizer. -/
theorem segre_original_source_euler_decomposition :
    (E₀) = (X₀) 0 • (D₀) 0 + (X₀) 1 • (D₀) 1 + (π₀) • (D₀) 3 := by
  apply derivation_ext_rational
  intro i
  simp only [sourceEuler_coordinate, Derivation.add_apply, Derivation.smul_apply,
    segre_original_source_chart_derivation_coordinate, smul_eq_mul]
  fin_cases i <;> simp [segreSourceChartMatrix, segreOriginalSourceUniformizer,
    segreOriginalSourceRulingParameter] <;>
    field_simp [segre_original_source_first_coordinate_ne_zero (K := K)] <;> ring_nf <;> simp

/-- Dividing a weight-alpha value by a positive-weight uniformizer
power constructs its exact reduced Euler weight, including order zero. -/
theorem derivation_uniformizer_power_factor_weight
    {F : Type*} [Field F] [Algebra K F]
    (E : Derivation K F F) (π f α : F) (hπ : π ≠ 0) (hEπ : E π = π) (j : ℕ)
    (hweight : E (π ^ j * f) = α * (π ^ j * f)) : E f = (α - (j : F)) * f := by
  have hpow : E (π ^ j) = (j : F) * π ^ j := by
    rw [Derivation.leibniz_pow, hEπ]
    cases j <;> simp [smul_eq_mul, nsmul_eq_mul, pow_succ] <;> ring
  rw [Derivation.leibniz, hpow] at hweight
  simp only [smul_eq_mul] at hweight
  apply mul_left_cancel₀ (pow_ne_zero j hπ)
  linear_combination hweight

/-- Homogeneity and the exact original output-row factorization
construct both row weights and slope weight minus one. Nonplanarity
supplies the required nonzero first output; no slope-weight or profile
assumption is imposed. -/
theorem segre_original_output_rows_construct_euler_weights
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (j : ℕ) (a f g : F₀)
    (hrows : ∀ r, algebraMap (MvPolynomial (Fin 4) K) F₀ (H r) =
      segreRulingLocalOutputRows j (π₀) (t₀) a f g r) :
    (E₀) f = ((d : F₀) - (j : F₀)) * f ∧
      (E₀) g = ((d : F₀) - (j : F₀)) * g ∧ (E₀) a = -a := by
  have hrowf : algebraMap (MvPolynomial (Fin 4) K) F₀ (H 0) = (π₀) ^ j * f := by
    simpa [segreRulingLocalOutputRows] using hrows 0
  have hrowg : algebraMap (MvPolynomial (Fin 4) K) F₀ (H 1) = (π₀) ^ j * g := by
    simpa [segreRulingLocalOutputRows] using hrows 1
  have hrowb : algebraMap (MvPolynomial (Fin 4) K) F₀ (H 2) = ((t₀) + (π₀) * a) * (π₀) ^ j * f := by
    simpa [segreRulingLocalOutputRows] using hrows 2
  have hpoly0 : H 0 ≠ 0 := (linearIndependent_of_componentsIndependent H hind).ne_zero 0
  have hsource0 : algebraMap (MvPolynomial (Fin 4) K) F₀ (H 0) ≠ 0 := by
    intro he
    apply hpoly0
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) F₀
    simpa only [map_zero] using he
  have hf : f ≠ 0 := by
    intro he
    apply hsource0
    rw [hrowf, he, mul_zero]
  have hEf : (E₀) f = ((d : F₀) - (j : F₀)) * f := by
    apply derivation_uniformizer_power_factor_weight (E₀) (π₀) f (d : F₀)
      segre_original_source_uniformizer_ne_zero segre_original_source_uniformizer_euler j
    rw [← hrowf]
    exact sourceEuler_homogeneous (H 0) (hH 0)
  have hEg : (E₀) g = ((d : F₀) - (j : F₀)) * g := by
    apply derivation_uniformizer_power_factor_weight (E₀) (π₀) g (d : F₀)
      segre_original_source_uniformizer_ne_zero segre_original_source_uniformizer_euler j
    rw [← hrowg]
    exact sourceEuler_homogeneous (H 1) (hH 1)
  have hratio : algebraMap (MvPolynomial (Fin 4) K) F₀ (H 2) /
      algebraMap (MvPolynomial (Fin 4) K) F₀ (H 0) = (t₀) + (π₀) * a := by
    rw [hrowb, hrowf]
    field_simp [segre_original_source_uniformizer_ne_zero (K := K)]
  have hEr : (E₀) (algebraMap (MvPolynomial (Fin 4) K) F₀ (H 2) /
      algebraMap (MvPolynomial (Fin 4) K) F₀ (H 0)) = 0 := by
    rw [Derivation.leibniz_div, sourceEuler_homogeneous (H 2) (hH 2), sourceEuler_homogeneous (H 0) (hH 0)]
    simp only [smul_eq_mul]
    ring
  rw [hratio, map_add, Derivation.leibniz, segre_original_source_parameter_euler_zero,
    segre_original_source_uniformizer_euler] at hEr
  simp only [zero_add, smul_eq_mul] at hEr
  refine ⟨hEf, hEg, ?_⟩
  apply mul_left_cancel₀ segre_original_source_uniformizer_ne_zero
  linear_combination hEr

end DimensionFourDependence
