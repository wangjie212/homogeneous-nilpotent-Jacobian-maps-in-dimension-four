import DimensionFourDependence.ExtendedGaussProjectiveStalkMaps
import DimensionFourDependence.LocalEquivOrderTransport

/-! # Actual global normalization orders are the original chart-local orders

The checked geometric source-stalk comparison preserves maximal-ideal
power membership. Thus order hypotheses on actual global normalization
germs become exactly the original given-prime local-model hypotheses.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- A specified element value under a local-ring isomorphism retains
all maximal-ideal order bounds. -/
theorem local_equiv_element_order_iff
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (x : A) (y : B) (h : e x = y) (a : ℕ) :
    x ∈ (IsLocalRing.maximalIdeal A) ^ a ↔ y ∈ (IsLocalRing.maximalIdeal B) ^ a := by
  rw [← h]
  exact (local_equiv_maximalIdeal_pow_mem_iff e x a).symm

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
local notation "zₑ" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q
local notation "Uₖ" => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  (MvPolynomial.X (s.symm none))

/-- Actual global source-function order bounds are exactly the
original tensor-normalization prime-localization bounds. -/
theorem extendedClosedGaussNormalizationSourceGerm_order_iff
    (q : PrimeSpectrum N₀) (r : R₀) (a : ℕ) :
    extendedClosedGaussNormalizationSourceGerm H I E hH e s q r ∈
        (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk (zₑ q))) ^ a ↔
      algebraMap N₀ (Localization.AtPrime q.asIdeal)
          (extendedClosedGaussTensorNormalizationSourceHom H I E s r) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) ^ a := by
  have h := local_equiv_element_order_iff
    (A := (Nₑ).presheaf.stalk (zₑ q)) (B := Localization.AtPrime q.asIdeal)
    (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q) _ _
    (extendedClosedGaussNormalizationTensorChartStalkIso_source_germ H I E hH e s q r) a
  convert! h using 1

/-- The geometric projective-source pullback order at the actual
global point is its original coordinate-local source order. -/
theorem extendedClosedGaussNormalizationProjectiveSourceGerm_order_iff
    (q : PrimeSpectrum N₀)
    (r : Γ(AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K), Uₖ))
    (a : ℕ) :
    extendedClosedGaussNormalizationProjectiveSourceGerm H I E hH e s q r ∈
        (IsLocalRing.maximalIdeal ((Nₑ).presheaf.stalk (zₑ q))) ^ a ↔
      algebraMap N₀ (Localization.AtPrime q.asIdeal)
          (algebraMap T₀ N₀ (extendedClosedGaussProjectiveSourceSectionHom H I E s r)) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) ^ a := by
  have h := local_equiv_element_order_iff
    (A := (Nₑ).presheaf.stalk (zₑ q)) (B := Localization.AtPrime q.asIdeal)
    (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q) _ _
    (extendedClosedGaussNormalizationTensorChartStalkIso_projective_source_germ H I E hH e s q r) a
  convert! h using 1

end DimensionFourDependence
