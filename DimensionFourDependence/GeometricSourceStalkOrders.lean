import DimensionFourDependence.ExtendedGaussSourceStalk
import DimensionFourDependence.OriginalSourceCanonicalOrders
import DimensionFourDependence.LocalEquivOrderTransport

/-! # All locally regular source functions retain their geometric orders

The complete actual source stalk map preserves every maximal-ideal
power at a codimension-one source-image point. The actual source stalk
is also identified as a discrete valuation ring.
-/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
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
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "N₀" => normalizationRing (S₀ ⊗[C₀] E)
local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q
local notation "Q₀" q:max => extendedClosedGaussTensorNormalizationSourcePrime H I E s q
local notation "hUₖ" => Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) K)
  (X (s.symm none)) (isHomogeneous_X (R := K) _) (by omega)

/-- The actual source-image stalk is a domain, by its specified
isomorphism with the original source prime localization. -/
theorem extendedClosedGaussNormalization_source_stalk_isDomain
    (q : PrimeSpectrum N₀) : IsDomain ((Pₖ).presheaf.stalk ((mₑ) (zₑ q))) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact Function.Injective.isDomain
    (extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q).toRingHom
    (extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q).injective

/-- Codimension one of the actual projective source-image point
makes its actual geometric stalk the original source-divisor DVR. -/
theorem extendedClosedGaussNormalization_source_stalk_isDiscreteValuationRing
    (q : PrimeSpectrum N₀)
    (hheight : ((hUₖ).primeIdealOf ⟨(mₑ) (zₑ q),
      extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal.height = 1) :
    letI : IsDomain ((Pₖ).presheaf.stalk ((mₑ) (zₑ q))) :=
      extendedClosedGaussNormalization_source_stalk_isDomain H I E hH e s q
    IsDiscreteValuationRing ((Pₖ).presheaf.stalk ((mₑ) (zₑ q))) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact by
    let : IsDomain ((Pₖ).presheaf.stalk ((mₑ) (zₑ q))) :=
      extendedClosedGaussNormalization_source_stalk_isDomain H I E hH e s q
    have hheight' : (Q₀ q).asIdeal.height = 1 := by
      rw [extendedClosedGaussTensorNormalizationSourcePrime_asIdeal]
      exact
        (extendedClosedGaussNormalizationTensorChartPoint_source_height_one_iff H I E hH e s q).mp hheight
    let : IsDiscreteValuationRing (Localization.AtPrime (Q₀ q).asIdeal) :=
      projective_source_height_one_isDVR s (Q₀ q).asIdeal hheight'
    exact local_equiv_isDiscreteValuationRing
      (A := (Pₖ).presheaf.stalk ((mₑ) (zₑ q)))
      (B := Localization.AtPrime (Q₀ q).asIdeal)
      (extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q)

/-- Every locally regular original source function, in the actual
source stalk, has exactly the same order bounds after actual geometric
pullback to the global normalization stalk. -/
theorem actual_global_projective_source_stalk_regular_order_iff
    [Module.Finite C₀ E] (q : PrimeSpectrum N₀)
    (hheight : ((hUₖ).primeIdealOf ⟨(mₑ) (zₑ q),
      extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q⟩).asIdeal.height = 1)
    (z : (Pₖ).presheaf.stalk ((mₑ) (zₑ q))) (a : ℕ) :
    (mₑ).stalkMap (zₑ q) z ∈
        (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk (zₑ q))) ^ a ↔
      z ∈ (IsLocalRing.maximalIdeal ((Pₖ).presheaf.stalk ((mₑ) (zₑ q)))) ^ a := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  exact by
    have hheight' : (Q₀ q).asIdeal.height = 1 := by
      rw [extendedClosedGaussTensorNormalizationSourcePrime_asIdeal]
      exact
        (extendedClosedGaussNormalizationTensorChartPoint_source_height_one_iff H I E hH e s q).mp hheight
    have hcanonical := actual_tensor_normalization_source_canonical_regular_orders H I E hH e s q hheight'
    have hn := local_equiv_element_order_iff
      (A := (Nₑ).presheaf.stalk (zₑ q)) (B := Localization.AtPrime q.asIdeal)
      (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q)
      ((mₑ).stalkMap (zₑ q) z)
      (Localization.localRingHom (Q₀ q).asIdeal q.asIdeal
        (extendedClosedGaussTensorNormalizationSourceHom H I E s)
        (extendedClosedGaussTensorNormalizationSourcePrime_asIdeal H I E s q)
        (extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q z))
      (extendedClosedGaussNormalizationSourceStalkEquiv_stalkMap H I E hH e s q z) a
    have hs := local_equiv_maximalIdeal_pow_mem_iff
      (A := (Pₖ).presheaf.stalk ((mₑ) (zₑ q)))
      (B := Localization.AtPrime (Q₀ q).asIdeal)
      (extendedClosedGaussNormalizationSourceStalkEquiv H I E hH e s q) z a
    exact hn.trans ((hcanonical _ a).trans hs)

end DimensionFourDependence
