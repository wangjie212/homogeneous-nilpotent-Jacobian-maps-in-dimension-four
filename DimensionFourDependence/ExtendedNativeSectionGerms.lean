import DimensionFourDependence.ExtendedOriginalSectionRepresentation
import DimensionFourDependence.ExtendedNormalizedChartGerms
import DimensionFourDependence.OriginalChartSectionStalkTransport

/-! # Original-section bound coefficients are the actual native global-section germs -/

namespace DimensionFourDependence

open AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "T" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)

local instance extendedNativeSectionGermsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedNativeSectionGermsDomain (a : Fin 4) : IsDomain (T a) :=
  original_tensor_pencil_chart_isDomain H I E (finSuccEquiv' a)

/-- The actual local coefficient germ of an actual native global
pencil section at an original normalized tensor-chart point. -/
noncomputable def extendedClosedGaussHyperplaneGlobalCoefficientGerm
    (s : Γ(M, ⊤)) (a : Fin 4) (Q : PrimeSpectrum (normalizationRing (T a))) :
    (N).presheaf.stalk (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) Q) :=
  (N).presheaf.germ (U a) _
    (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) Q)
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a)

/-- The canonical normalized coefficient used by the original
section bound is exactly the actual chart regular function's coefficient. -/
theorem extendedClosedGaussHyperplaneOriginalNormalizationCoefficient_eq
    (s : Γ(M, ⊤)) (a : Fin 4) :
    originalChartSectionNormalizationCoefficient
      (originalTensorPencilCoordinate H I E (finSuccEquiv' a))
      (extendedClosedGaussOriginalFrameCoordinates H I E hH e (finSuccEquiv' a))
      (extendedClosedGaussHyperplaneOriginalNormalizedSection H I E hH e (finSuccEquiv' a) s)
      (finSuccEquiv' a)
      (extendedClosedGaussOriginalFrameCoordinates_ne_zero H I E hH e (finSuccEquiv' a) _)
      (extendedClosedGaussOriginalFrameCoordinates_ratios H I E hH e (finSuccEquiv' a)) =
      extendedClosedGaussNormalizedChartSectionEquiv H I E hH e (finSuccEquiv' a)
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a) := by
  apply Subtype.ext
  change ((extendedClosedGaussHyperplaneOriginalNormalizedSection H I E hH e (finSuccEquiv' a) s).coefficient
    ((finSuccEquiv' a).symm none) : FractionRing (T a)) =
      extendedClosedGaussHyperplaneOriginalCoefficient H I E hH e s a
  exact (congrArg (fun i : Fin 4 =>
    ((extendedClosedGaussHyperplaneOriginalNormalizedSection H I E hH e (finSuccEquiv' a) s).coefficient i :
      FractionRing (T a))) (finSuccEquiv'_symm_none a)).trans
        (extendedClosedGaussHyperplaneOriginalNormalizedSection_original_coefficient H I E hH e s a)

/-- The canonical global stalk germ used by the original section
bound is precisely the actual germ of the actual native global section's
regular original-frame coefficient. -/
theorem extendedClosedGaussHyperplaneOriginalSectionStalkGerm_eq
    (s : Γ(M, ⊤)) (a : Fin 4) (Q : PrimeSpectrum (normalizationRing (T a))) :
    originalChartSectionStalkGerm Q.asIdeal
      (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e (finSuccEquiv' a) Q)
      (originalTensorPencilCoordinate H I E (finSuccEquiv' a))
      (extendedClosedGaussOriginalFrameCoordinates H I E hH e (finSuccEquiv' a))
      (extendedClosedGaussHyperplaneOriginalNormalizedSection H I E hH e (finSuccEquiv' a) s)
      (finSuccEquiv' a)
      (extendedClosedGaussOriginalFrameCoordinates_ne_zero H I E hH e (finSuccEquiv' a) _)
      (extendedClosedGaussOriginalFrameCoordinates_ratios H I E hH e (finSuccEquiv' a)) =
      extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e s a Q := by
  let β := extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e (finSuccEquiv' a) Q
  apply β.injective
  exact (original_chart_section_stalk_germ_local_value Q.asIdeal β
    (originalTensorPencilCoordinate H I E (finSuccEquiv' a))
    (extendedClosedGaussOriginalFrameCoordinates H I E hH e (finSuccEquiv' a))
    (extendedClosedGaussHyperplaneOriginalNormalizedSection H I E hH e (finSuccEquiv' a) s)
    (finSuccEquiv' a)
    (extendedClosedGaussOriginalFrameCoordinates_ne_zero H I E hH e (finSuccEquiv' a) _)
    (extendedClosedGaussOriginalFrameCoordinates_ratios H I E hH e (finSuccEquiv' a))).trans
      ((congrArg (algebraMap (normalizationRing (T a)) (Localization.AtPrime Q.asIdeal))
        (extendedClosedGaussHyperplaneOriginalNormalizationCoefficient_eq H I E hH e s a)).trans
          (extendedClosedGaussNormalizationTensorChartStalkIso_regular_germ H I E hH e (finSuccEquiv' a) Q
            (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a)).symm)

/-- Nonzero native global sections have nonzero actual local
original-frame coefficient germs. -/
theorem extendedClosedGaussHyperplaneGlobalCoefficientGerm_ne_zero
    (s : Γ(M, ⊤)) (hs : s ≠ 0) (a : Fin 4)
    (Q : PrimeSpectrum (normalizationRing (T a))) :
    extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e s a Q ≠ 0 := by
  intro hz
  apply extendedClosedGaussHyperplaneGlobalCoefficient_ne_zero H I E hH e s hs a
  apply germ_injective_of_isIntegral N
    (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) Q)
    (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) Q)
  exact hz.trans (map_zero _).symm

end DimensionFourDependence
