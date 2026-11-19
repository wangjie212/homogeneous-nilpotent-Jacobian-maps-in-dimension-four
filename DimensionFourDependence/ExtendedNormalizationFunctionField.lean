import DimensionFourDependence.ExtendedNormalizedChartSections
import DimensionFourDependence.AffineChartFunctionFieldEquiv

/-! # The original normalized pencil charts in the scheme's own function field -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

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
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none) ⊗[C₀] E
local notation "X" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" => extendedClosedGaussNormalizationChartOpen H I E hH e s

local instance : IsIntegral X := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance : IsDomain T₀ := original_tensor_pencil_chart_isDomain H I E s

/-- Each original inverse coordinate chart is affine on the actual
normalization formed after coefficient extension. -/
theorem extendedClosedGaussNormalizationChartOpen_isAffineOpen : IsAffineOpen U :=
  IsAffine.of_isIso (extendedClosedGaussNormalizationTensorChartIso H I E hH e s).hom

/-- None of the four original coordinate opens disappears on the
actual normalization. -/
theorem extendedClosedGaussNormalizationChartOpen_nonempty : Nonempty U :=
  ⟨(extendedClosedGaussNormalizationTensorChartIso H I E hH e s).inv
    (⊥ : PrimeSpectrum (normalizationRing T₀))⟩

local instance : Nonempty U := extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e s

/-- The original tensor chart's fraction field is the actual normalized
pencil's own function field, with the regular section identification fixed. -/
noncomputable def extendedClosedGaussNormalizedChartFunctionFieldEquiv :
    FractionRing T₀ ≃+* (X).functionField := by
  let : IsFractionRing (normalizationRing T₀) (FractionRing T₀) :=
    normalizationRing_isFractionRing T₀
  exact affineChartFunctionFieldEquiv X U
    (extendedClosedGaussNormalizationChartOpen_isAffineOpen H I E hH e s)
    (normalizationRing T₀) (FractionRing T₀)
    (extendedClosedGaussNormalizedChartSectionEquiv H I E hH e s)

/-- Every actual normalized chart function retains its original tensor
value under the identification with the scheme's generic-point stalk. -/
theorem extendedClosedGaussNormalizedChartFunctionFieldEquiv_section (r : Γ(X, U)) :
    extendedClosedGaussNormalizedChartFunctionFieldEquiv H I E hH e s
      (extendedClosedGaussNormalizedChartSectionValue H I E hH e s r) =
        (X).germToFunctionField U r := by
  let : IsFractionRing (normalizationRing T₀) (FractionRing T₀) :=
    normalizationRing_isFractionRing T₀
  exact affineChartFunctionFieldEquiv_section X U
    (extendedClosedGaussNormalizationChartOpen_isAffineOpen H I E hH e s)
    (normalizationRing T₀) (FractionRing T₀)
    (extendedClosedGaussNormalizedChartSectionEquiv H I E hH e s) r

/-- Original rational coefficients agree with the actual local-ring
germs at every point of the normalized chart. -/
theorem extendedClosedGaussNormalizedChartFunctionFieldEquiv_section_at_point
    (r : Γ(X, U)) (p : U) :
    extendedClosedGaussNormalizedChartFunctionFieldEquiv H I E hH e s
      (extendedClosedGaussNormalizedChartSectionValue H I E hH e s r) =
        schemeRationalSectionFunction X U r p := by
  rw [extendedClosedGaussNormalizedChartFunctionFieldEquiv_section,
    schemeRationalSectionFunction_eq_generic]

end DimensionFourDependence
