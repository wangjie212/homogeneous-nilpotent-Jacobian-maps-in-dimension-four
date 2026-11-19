import DimensionFourDependence.GlobalCanonicalRationalOrders
import DimensionFourDependence.RationalStalkPullbackComparison

/-! # Rational source valuations through the actual global geometric map

The actual codimension-one source-image point gives a rational source
pullback extending every value of the actual geometric stalk map, with
unchanged normalized valuations in the actual global normalization DVR.
-/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 8000000
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
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "N₀" => normalizationRing (S₀ ⊗[C₀] E)
local notation "L₀" => projectiveCoordinateChartField (C := K) x₀ (s.symm none)
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q
local notation "Q₀" q:max => extendedClosedGaussTensorNormalizationSourcePrime H I E s q
local notation "hUₖ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K)
  (X (s.symm none)) (isHomogeneous_X (R := K) _) (by omega)

/-- Codimension one of the actual projective source-image point
gives height one of its specified original source prime. -/
theorem extendedClosedGaussNormalization_source_image_height_one
    (q : PrimeSpectrum N₀)
    (hheight : ((hUₖ).primeIdealOf ⟨(mₑ) (zₑ q),
      extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal.height = 1) :
    (Q₀ q).asIdeal.height = 1 := by
  rw [extendedClosedGaussTensorNormalizationSourcePrime_asIdeal]
  exact (extendedClosedGaussNormalizationTensorChartPoint_source_height_one_iff H I E hH e s q).mp hheight

/-- With the actual geometric source-divisor condition, every original
rational source function has the same normalized valuation after actual
global pullback. That pullback extends the complete actual source stalk
map, and the target global normalization stalk is itself a DVR. -/
theorem actual_global_projective_source_rational_stalk_orders
    [Module.Finite C₀ E] (q : PrimeSpectrum N₀)
    (hheight : ((hUₖ).primeIdealOf ⟨(mₑ) (zₑ q),
      extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal.height = 1) :
    let hheight' := extendedClosedGaussNormalization_source_image_height_one H I E hH e s q hheight
    letI : IsDiscreteValuationRing (Localization.AtPrime (Q₀ q).asIdeal) :=
      projective_source_height_one_isDVR s (Q₀ q).asIdeal hheight'
    letI : Algebra (Localization.AtPrime (Q₀ q).asIdeal) L₀ := primeLocalizationFractionAlgebra (Q₀ q).asIdeal
    letI : IsFractionRing (Localization.AtPrime (Q₀ q).asIdeal) L₀ := projective_source_divisor_isFractionRing s (Q₀ q).asIdeal
    letI : IsDomain ((Nₑ).presheaf.stalk (zₑ q)) := extendedClosedGaussNormalization_global_stalk_isDomain H I E hH e s q
    RationalStalkPullbackComparison
      (S := (Pₖ).presheaf.stalk ((mₑ) (zₑ q))) (O := Localization.AtPrime (Q₀ q).asIdeal)
      (A := (Nₑ).presheaf.stalk (zₑ q)) (F := L₀)
      (extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q)
      ((mₑ).stalkMap (zₑ q)).hom := by
  let hheight' := extendedClosedGaussNormalization_source_image_height_one H I E hH e s q hheight
  let : IsDiscreteValuationRing (Localization.AtPrime (Q₀ q).asIdeal) :=
    projective_source_height_one_isDVR s (Q₀ q).asIdeal hheight'
  let : Algebra (Localization.AtPrime (Q₀ q).asIdeal) L₀ := primeLocalizationFractionAlgebra (Q₀ q).asIdeal
  let : IsFractionRing (Localization.AtPrime (Q₀ q).asIdeal) L₀ := projective_source_divisor_isFractionRing s (Q₀ q).asIdeal
  let : IsDomain ((Nₑ).presheaf.stalk (zₑ q)) := extendedClosedGaussNormalization_global_stalk_isDomain H I E hH e s q
  have hcompat := extendedClosedGaussNormalizationSourceLocalHom_stalkMap H I E hH e s q
  have hcanonical := actual_global_normalization_source_canonical_rational_orders H I E hH e s q hheight'
  have hresult := canonical_rational_comparison_to_stalk_pullback
    (S := (Pₖ).presheaf.stalk ((mₑ) (zₑ q))) (O := Localization.AtPrime (Q₀ q).asIdeal)
    (A := (Nₑ).presheaf.stalk (zₑ q)) (F := L₀)
    (extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q)
    (extendedClosedGaussNormalizationSourceLocalHom H I E hH e s q)
    ((mₑ).stalkMap (zₑ q)).hom
    hcompat hcanonical
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  exact hresult

end DimensionFourDependence
