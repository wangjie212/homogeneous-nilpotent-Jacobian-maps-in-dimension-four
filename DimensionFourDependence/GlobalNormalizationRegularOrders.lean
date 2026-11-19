import DimensionFourDependence.GlobalNormalizationMultiplicity
import DimensionFourDependence.ProjectiveCanonicalRegularOrders
import DimensionFourDependence.ExtendedGaussSourcePoint
import DimensionFourDependence.OriginalSourcePrimeRegularOrders

/-! # Exact original-source orders in actual global normalization stalks

The actual global source germs preserve every order bound at a
codimension-one original source-image point.
-/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
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
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K) x₀ (s.symm none)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N₀" => normalizationRing T₀
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q
local notation "Q₀" q:max => PrimeSpectrum.asIdeal
  (extendedClosedGaussTensorNormalizationSourcePrime H I E s q)
local notation "hUₖ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K)
  (X (s.symm none)) (isHomogeneous_X (R := K) _) (by omega)

/-- Every original source function has exactly the same order bounds
in the actual global normalization stalk and its source-divisor DVR. -/
theorem actual_global_normalization_source_regular_order_iff
    [Module.Finite C₀ E] (q : PrimeSpectrum N₀)
    (hheight : (Q₀ q).height = 1) (r : R₀) (a : ℕ) :
    extendedClosedGaussNormalizationSourceGerm H I E hH e s q r ∈
        (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk (zₑ q))) ^ a ↔
      algebraMap R₀ (Localization.AtPrime (Q₀ q)) r ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime (Q₀ q))) ^ a := by
  have hglobal := extendedClosedGaussNormalizationSourceGerm_order_iff H I E hH e s q r a
  exact hglobal.trans
    (actual_tensor_normalization_source_regular_order_iff H I E hH e s q hheight r a)

/-- The same exact comparison with codimension one imposed on the
actual projective source-image point and actual pulled-back sections. -/
theorem actual_global_projective_source_regular_order_iff
    [Module.Finite C₀ E] (q : PrimeSpectrum N₀)
    (hheight : ((hUₖ).primeIdealOf ⟨(mₑ) (zₑ q),
      extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal.height = 1)
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K),
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none)))) (a : ℕ) :
    extendedClosedGaussNormalizationProjectiveSourceGerm H I E hH e s q r ∈
        (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk (zₑ q))) ^ a ↔
      algebraMap R₀ (Localization.AtPrime (Q₀ q))
          (originalProjectiveAffineSectionEquiv (K := K) (s.symm none) r) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime (Q₀ q))) ^ a := by
  have hheight' : (Q₀ q).height = 1 := by
    rw [extendedClosedGaussTensorNormalizationSourcePrime_asIdeal]
    exact
      (extendedClosedGaussNormalizationTensorChartPoint_source_height_one_iff H I E hH e s q).mp hheight
  rw [extendedClosedGaussNormalizationProjectiveSourceGerm_eq_source_germ]
  exact actual_global_normalization_source_regular_order_iff H I E hH e s q hheight'
    (originalProjectiveAffineSectionEquiv (K := K) (s.symm none) r) a

end DimensionFourDependence
