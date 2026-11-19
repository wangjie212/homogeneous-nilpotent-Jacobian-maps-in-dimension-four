import DimensionFourDependence.ExtendedGaussNormalizationSourceDiagram
import DimensionFourDependence.OriginalProjectiveChartRing
import DimensionFourDependence.AffineSourcePoint

/-! # The actual global source-image point has the original contracted prime

The actual projection to the original projective source has the same
prime and height as its specified original source-ring contraction.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N₀" => normalizationRing T₀
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "jₑ" => extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q
local notation "Uₖ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none))
local notation "hUₖ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K)
  (X (s.symm none)) (isHomogeneous_X (R := K) _) (by omega)

/-- The actual projective source-image prime is the original source
contraction transported through its actual projective section isomorphism. -/
theorem extendedClosedGaussNormalizationTensorChartPoint_source_prime
    (q : PrimeSpectrum N₀) :
    ((hUₖ).primeIdealOf ⟨(mₑ) (zₑ q),
      extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal =
      (q.asIdeal.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s)).comap
        (originalProjectiveAffineSectionEquiv (K := K) (s.symm none)).toRingHom := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact by
    let U : (AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)).affineOpens :=
      ⟨Uₖ, hUₖ⟩
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    let φ : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K), U.1) ⟶ CommRingCat.of N₀ :=
      CommRingCat.ofHom ((algebraMap T₀ N₀).comp
        (extendedClosedGaussProjectiveSourceSectionHom H I E s))
    have h := affineSourceDiagram_primeIdealOf (CommRingCat.of N₀) U φ ((jₑ) ≫ (mₑ))
      (extendedClosedGaussNormalizationTensorChartInclusion_to_source H I E hH e s) q
    unfold extendedClosedGaussNormalizationTensorChartPoint
    convert! congrArg PrimeSpectrum.asIdeal h using 1

/-- The height of the actual projective source-image point is the
height of the original source-ring contraction. -/
theorem extendedClosedGaussNormalizationTensorChartPoint_source_height
    (q : PrimeSpectrum N₀) :
    ((hUₖ).primeIdealOf ⟨(mₑ) (zₑ q),
      extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal.height =
      (q.asIdeal.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s)).height := by
  rw [extendedClosedGaussNormalizationTensorChartPoint_source_prime]
  exact (originalProjectiveAffineSectionEquiv (K := K) (s.symm none)).height_comap _

/-- Codimension one for the actual source-image point is exactly the
height-one condition needed by the original source-divisor local model. -/
theorem extendedClosedGaussNormalizationTensorChartPoint_source_height_one_iff
    (q : PrimeSpectrum N₀) :
    ((hUₖ).primeIdealOf ⟨(mₑ) (zₑ q),
      extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal.height = 1 ↔
      (q.asIdeal.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s)).height = 1 := by
  rw [extendedClosedGaussNormalizationTensorChartPoint_source_height]

end DimensionFourDependence
