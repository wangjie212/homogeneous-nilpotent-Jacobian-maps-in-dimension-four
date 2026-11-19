import DimensionFourDependence.AffineChartSectionNaturality
import DimensionFourDependence.ExtendedNormalizedChartSections

/-! # Actual regular normalized chart functions retain their original global-stalk values -/

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
local notation "N₀" => normalizationRing T₀
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" => extendedClosedGaussNormalizationChartOpen H I E hH e s
local notation "y" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q

local instance extendedNormalizedChartGermsDomain : IsDomain T₀ :=
  original_tensor_pencil_chart_isDomain H I E s

/-- The actual global point supplied by an original normalized
tensor prime lies in that same original normalized coordinate open. -/
theorem extendedClosedGaussNormalizationTensorChartPoint_mem_chart (q : PrimeSpectrum N₀) :
    y q ∈ U := by
  unfold extendedClosedGaussNormalizationTensorChartPoint
    extendedClosedGaussNormalizationTensorChartInclusion
  exact (extendedClosedGaussNormalizationTensorChartIso H I E hH e s).inv q |>.property

/-- The actual global germ of every actual regular normalized chart
function has exactly its original normalized coefficient in the original
prime localization under the actual chart-stalk isomorphism. -/
theorem extendedClosedGaussNormalizationTensorChartStalkIso_regular_germ
    (q : PrimeSpectrum N₀) (r : Γ(N, U)) :
    extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q
        ((N).presheaf.germ U (y q)
          (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e s q) r) =
      algebraMap N₀ (Localization.AtPrime q.asIdeal)
        (extendedClosedGaussNormalizedChartSectionEquiv H I E hH e s r) := by
  let j := extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s
  let : IsOpenImmersion j :=
    extendedClosedGaussNormalizationTensorChartInclusion_isOpenImmersion H I E hH e s
  have htop : ⊤ ≤ j ⁻¹ᵁ U := by
    intro p hp
    exact (extendedClosedGaussNormalizationTensorChartIso H I E hH e s).inv p |>.property
  have hg := schemeAffineOpenImmersionStalkIso_germ (CommRingCat.of N₀) j q U htop r
  have hc := affineChartSectionEquiv_appLE U (CommRingCat.of N₀)
    (extendedClosedGaussNormalizationTensorChartIso H I E hH e s) htop r
  unfold extendedClosedGaussNormalizationTensorChartStalkIso
    extendedClosedGaussNormalizationTensorChartPoint
  exact hg.trans (congrArg (algebraMap N₀ (Localization.AtPrime q.asIdeal)) hc)

end DimensionFourDependence
