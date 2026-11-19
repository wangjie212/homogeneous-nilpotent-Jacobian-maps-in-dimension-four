import DimensionFourDependence.SegreRulingLocalJacobianReduction
import DimensionFourDependence.VerticalDerivation
import DimensionFourDependence.StandardRulingQuadric

/-! # The Segre chart and tangent chain rule in the original rational source field -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]

local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "X₀" => rationalCoordinate (K := K) (n := 4)

/-- The original ruling parameter is the ratio of the lower-left and
upper-left matrix entries. -/
noncomputable def segreOriginalSourceRulingParameter : F₀ := (X₀) 2 / (X₀) 0

/-- The original quadric uniformizer on the first-coordinate chart is
`x4 - (x3/x1)*x2 = det(X)/x1`. -/
noncomputable def segreOriginalSourceUniformizer : F₀ :=
  (X₀) 3 - segreOriginalSourceRulingParameter (K := K) * (X₀) 1

/-- The differential of `(x,y,t,pi) -> (x,y,t*x,t*y+pi)` in original
source coordinates. -/
def segreSourceChartMatrix {F : Type*} [CommRing F] (t x y : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; t, 0, x, 0; 0, t, y, 1]

/-- The coordinate derivations of this chart are constructed as actual
vector fields on the original source fraction field. -/
noncomputable def segreOriginalSourceChartDerivation (i : Fin 4) : Derivation K F₀ F₀ :=
  sourceVectorDerivation (fun r => segreSourceChartMatrix
    (segreOriginalSourceRulingParameter (K := K)) ((X₀) 0) ((X₀) 1) r i)

/-- Values on all original source coordinates, not only on a new
independent coordinate presentation. -/
theorem segre_original_source_chart_derivation_coordinate (i r : Fin 4) :
    segreOriginalSourceChartDerivation (K := K) i ((X₀) r) =
      segreSourceChartMatrix (segreOriginalSourceRulingParameter (K := K)) ((X₀) 0) ((X₀) 1) r i :=
  sourceVectorDerivation_coordinate _ _

/-- The chosen original source coordinate is nonzero in its actual
rational function field. -/
theorem segre_original_source_first_coordinate_ne_zero : (X₀) 0 ≠ 0 := by
  intro he
  apply MvPolynomial.X_ne_zero (R := K) (0 : Fin 4)
  apply IsFractionRing.injective (MvPolynomial (Fin 4) K) F₀
  simpa only [rationalCoordinate, map_zero] using he

/-- The specified uniformizer retains the original determinant
polynomial and its exact original first-coordinate denominator. -/
theorem segre_original_source_uniformizer_eq_determinant :
    segreOriginalSourceUniformizer (K := K) =
      algebraMap (MvPolynomial (Fin 4) K) F₀ (standardRulingPolynomial (F := K)) / (X₀) 0 := by
  have he : algebraMap (MvPolynomial (Fin 4) K) F₀ (standardRulingPolynomial (F := K)) =
      (X₀) 0 * (X₀) 3 - (X₀) 1 * (X₀) 2 := by
    simp [standardRulingPolynomial, rationalCoordinate]
  rw [he]
  unfold segreOriginalSourceUniformizer segreOriginalSourceRulingParameter
  field_simp [segre_original_source_first_coordinate_ne_zero (K := K)]

/-- The original quadric uniformizer is nonzero in the generic source
field, as required by the faithful tangent-frame realization. -/
theorem segre_original_source_uniformizer_ne_zero : segreOriginalSourceUniformizer (K := K) ≠ 0 := by
  rw [segre_original_source_uniformizer_eq_determinant]
  apply div_ne_zero
  · intro he
    apply standardRulingPolynomial_ne_zero (F := K)
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) F₀
    simpa only [map_zero] using he
  · exact segre_original_source_first_coordinate_ne_zero

/-- The ruling parameter really is the third chart coordinate. -/
theorem segre_original_source_chart_derivation_parameter (i : Fin 4) :
    segreOriginalSourceChartDerivation (K := K) i (segreOriginalSourceRulingParameter (K := K)) =
      if i = 2 then 1 else 0 := by
  rw [segreOriginalSourceRulingParameter, Derivation.leibniz_div]
  simp only [segre_original_source_chart_derivation_coordinate, smul_eq_mul]
  fin_cases i <;> simp [segreSourceChartMatrix, segreOriginalSourceRulingParameter] <;>
    field_simp [segre_original_source_first_coordinate_ne_zero (K := K)] <;> ring_nf <;> simp

/-- The quadric equation divided by the first coordinate really is
the fourth chart coordinate for the constructed original derivations. -/
theorem segre_original_source_chart_derivation_uniformizer (i : Fin 4) :
    segreOriginalSourceChartDerivation (K := K) i (segreOriginalSourceUniformizer (K := K)) =
      if i = 3 then 1 else 0 := by
  rw [segreOriginalSourceUniformizer, map_sub, Derivation.leibniz]
  simp only [segre_original_source_chart_derivation_parameter,
    segre_original_source_chart_derivation_coordinate, smul_eq_mul]
  fin_cases i <;> simp [segreSourceChartMatrix] <;> ring

/-- The actual polynomial Jacobian transforms to the constructed chart
Jacobian by its source differential, with every original partial retained. -/
theorem segre_original_source_chart_polynomial_jacobian
    (H : Fin 4 → MvPolynomial (Fin 4) K) :
    (Matrix.of fun r i => segreOriginalSourceChartDerivation (K := K) i
      (algebraMap (MvPolynomial (Fin 4) K) F₀ (H r))) =
      (jac H).map (algebraMap (MvPolynomial (Fin 4) K) F₀) *
        segreSourceChartMatrix (segreOriginalSourceRulingParameter (K := K)) ((X₀) 0) ((X₀) 1) := by
  ext r i
  simp only [Matrix.of_apply, segreOriginalSourceChartDerivation, sourceVectorDerivation_apply,
    rationalPartial_polynomial, Matrix.mul_apply, Matrix.map_apply, jac]
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

/-- The ruling tangent variation matrix constructs the exact same
original source frame through the chart differential. -/
theorem segre_original_source_chart_variation_frame :
    segreSourceChartMatrix (segreOriginalSourceRulingParameter (K := K)) ((X₀) 0) ((X₀) 1) *
      segreRulingChartVariationMatrix (segreOriginalSourceUniformizer (K := K))
        (((X₀) 0)⁻¹) ((X₀) 1 / (X₀) 0) =
      segreRulingSourceTangentFrame (segreOriginalSourceRulingParameter (K := K))
        (segreOriginalSourceUniformizer (K := K)) := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [segreSourceChartMatrix, segreRulingChartVariationMatrix, segreRulingSourceTangentFrame,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
      field_simp [segre_original_source_first_coordinate_ne_zero (K := K)] <;> ring_nf <;> simp

/-- The chain-rule input needed by the regular tangent reduction is
constructed from the actual original polynomial Jacobian and source
coordinates, without a supplied transformed Jacobian. -/
theorem segre_original_source_jacobian_tangent_chain_rule
    (H : Fin 4 → MvPolynomial (Fin 4) K) :
    (jac H).map (algebraMap (MvPolynomial (Fin 4) K) F₀) *
        segreRulingSourceTangentFrame (segreOriginalSourceRulingParameter (K := K))
          (segreOriginalSourceUniformizer (K := K)) =
      (Matrix.of fun r i => segreOriginalSourceChartDerivation (K := K) i
        (algebraMap (MvPolynomial (Fin 4) K) F₀ (H r))) *
      segreRulingChartVariationMatrix (segreOriginalSourceUniformizer (K := K))
        (((X₀) 0)⁻¹) ((X₀) 1 / (X₀) 0) := by
  rw [← segre_original_source_chart_variation_frame, ← Matrix.mul_assoc,
    ← segre_original_source_chart_polynomial_jacobian]

end DimensionFourDependence
