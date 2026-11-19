import DimensionFourDependence.ExtendedNormalizationHyperplaneSheaf

/-! # Actual global hyperplane sections supply original integral chart coefficients -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e
local notation "T" a:max => projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[closedGaussParameterField H I] E

local instance : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance (a : Fin 4) : IsDomain (T a) :=
  original_tensor_pencil_chart_isDomain H I E (finSuccEquiv' a)
local instance (a : Fin 4) : Nonempty (U a) :=
  extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e (finSuccEquiv' a)

/-- An actual global section's common rational numerator, inside the
actual normalized pencil's own function field. -/
noncomputable def extendedClosedGaussHyperplaneGlobalValue (s : Γ(M, ⊤)) : (N).functionField :=
  rationalFrameGlobalSectionValue N (fun a : Fin 4 => U a) w s

/-- The actual regular coefficient of a global sheaf section in
each of the original tensor-normalization frame charts. -/
noncomputable def extendedClosedGaussHyperplaneGlobalCoefficient
    (s : Γ(M, ⊤)) (a : Fin 4) : Γ(N, U a) :=
  rationalFrameGlobalCoefficient N (fun a : Fin 4 => U a) w
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e) s a

/-- The original regular frame coefficient retains the actual global
section's common rational numerator at every point of the chart. -/
theorem extendedClosedGaussHyperplaneGlobalCoefficient_value
    (s : Γ(M, ⊤)) (a : Fin 4) (p : U a) :
    extendedClosedGaussHyperplaneGlobalValue H I E hH e s =
      w a * schemeRationalSectionFunction N (U a)
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a) p :=
  rationalFrameGlobalCoefficient_value N (fun a : Fin 4 => U a) w
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e) s a p

/-- A nonzero actual global section has a nonzero coefficient on
every original tensor-normalization chart. -/
theorem extendedClosedGaussHyperplaneGlobalCoefficient_ne_zero
    (s : Γ(M, ⊤)) (hs : s ≠ 0) (a : Fin 4) :
    extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a ≠ 0 :=
  rationalFrameGlobalCoefficient_ne_zero N (fun a : Fin 4 => U a) w
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e) s hs a

/-- The original chart's rational coefficient of an actual global
hyperplane section, obtained from its actual regular coefficient. -/
noncomputable def extendedClosedGaussHyperplaneOriginalCoefficient
    (s : Γ(M, ⊤)) (a : Fin 4) : FractionRing (T a) :=
  extendedClosedGaussNormalizedChartSectionValue H I E hH e (finSuccEquiv' a)
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a)

/-- Every actual global hyperplane section supplies an integral
coefficient over each entire original tensor chart ring. -/
theorem extendedClosedGaussHyperplaneOriginalCoefficient_isIntegral
    (s : Γ(M, ⊤)) (a : Fin 4) :
    IsIntegral (T a) (extendedClosedGaussHyperplaneOriginalCoefficient H I E hH e s a) :=
  extendedClosedGaussNormalizedChartSectionValue_isIntegral H I E hH e (finSuccEquiv' a) _

/-- Nonzero actual global sections supply nonzero original rational
coefficients, with no nonvanishing assumption on supplied frame data. -/
theorem extendedClosedGaussHyperplaneOriginalCoefficient_ne_zero
    (s : Γ(M, ⊤)) (hs : s ≠ 0) (a : Fin 4) :
    extendedClosedGaussHyperplaneOriginalCoefficient H I E hH e s a ≠ 0 := by
  intro hz
  apply extendedClosedGaussHyperplaneGlobalCoefficient_ne_zero H I E hH e s hs a
  exact (extendedClosedGaussNormalizedChartSectionValue_injective H I E hH e (finSuccEquiv' a))
    (hz.trans (map_zero _).symm)

/-- Original integral coefficients retain exactly the same common
rational numerator under the constructed original-chart field identification. -/
theorem extendedClosedGaussHyperplaneOriginalCoefficient_field_value
    (s : Γ(M, ⊤)) (a : Fin 4) :
    w a * extendedClosedGaussNormalizedChartFunctionFieldEquiv H I E hH e (finSuccEquiv' a)
        (extendedClosedGaussHyperplaneOriginalCoefficient H I E hH e s a) =
      extendedClosedGaussHyperplaneGlobalValue H I E hH e s := by
  let p : U a := Classical.choice (inferInstance : Nonempty (U a))
  rw [extendedClosedGaussHyperplaneOriginalCoefficient,
    extendedClosedGaussNormalizedChartFunctionFieldEquiv_section_at_point
      H I E hH e (finSuccEquiv' a) _ p]
  exact (extendedClosedGaussHyperplaneGlobalCoefficient_value H I E hH e s a p).symm

end DimensionFourDependence
