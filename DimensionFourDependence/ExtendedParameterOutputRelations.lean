import DimensionFourDependence.ExtendedOriginalHomogeneousRelations
import DimensionFourDependence.ProjectiveLineAtlasPoints

/-! # The actual original output covector relations persist on the normalized pencil -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedParameterOutputRelationsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedParameterOutputRelationsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual ruling-linear source-form section has exactly the
original coefficient-weighted component value in the native field. -/
theorem extendedClosedGaussOutputLinearPolynomial_value (c : Fin 4 → E) :
    aeval w (extendedClosedGaussOutputLinearPolynomial H I E c) =
      ∑ i, algebraMap E (N).functionField (c i) *
        aeval w (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)) := by
  simp [extendedClosedGaussOutputLinearPolynomial, Algebra.smul_def]

/-- Every actual output-covector relation over the original closed
parameter field survives on the actual normalized pencil over the given
algebraic extension. The relation is supplied only in the original source. -/
theorem extendedClosedGauss_original_output_covector_relation
    (c : Fin 4 → C₀)
    (hrel : ∑ i, algebraMap C₀ (FractionRing (MvPolynomial (Fin 4) K)) (c i) *
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i) = 0) :
    ∑ i, algebraMap E (N).functionField (algebraMap C₀ E (c i)) *
      aeval w (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) (H i)) = 0 := by
  let P : MvPolynomial (Fin 4) C₀ :=
    ∑ i, MvPolynomial.C (c i) * MvPolynomial.map (algebraMap K C₀) (H i)
  have hP : P.IsHomogeneous d := by
    apply IsHomogeneous.sum
    intro i hi
    exact ((hH i).map (algebraMap K C₀)).C_mul (c i)
  have hzero : aeval (rationalCoordinate (K := K) (n := 4)) P = 0 := by
    simpa only [P, map_sum, map_mul, aeval_C, aeval_map_algebra_extension,
      rationalCoordinate_aeval] using hrel
  have hv := extendedClosedGauss_original_homogeneous_relation H I E hH e P hP hzero
  simpa only [P, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_map, aeval_C,
    extendedClosedGaussSourceCoefficientHom] using hv

/-- The actual regular output-linear form of an original source
covector relation is identically zero in the native pencil field. -/
theorem extendedClosedGauss_original_output_linear_form_zero
    (c : Fin 4 → C₀)
    (hrel : ∑ i, algebraMap C₀ (FractionRing (MvPolynomial (Fin 4) K)) (c i) *
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i) = 0) :
    aeval w (extendedClosedGaussOutputLinearPolynomial H I E (fun i => algebraMap C₀ E (c i))) = 0 := by
  rw [extendedClosedGaussOutputLinearPolynomial_value]
  exact extendedClosedGauss_original_output_covector_relation H I E hH e c hrel

end DimensionFourDependence
