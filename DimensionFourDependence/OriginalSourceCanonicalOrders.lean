import DimensionFourDependence.OriginalSourcePrimeRegularOrders

/-! # The entire original source-local map preserves regular orders

The canonical order comparison is retained for every element of the
source prime localization, using the specified original source map.
-/

namespace DimensionFourDependence

open AlgebraicGeometry
open scoped TensorProduct

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
local notation "Q₀" q:max => extendedClosedGaussTensorNormalizationSourcePrime H I E s q

include hH e in
/-- The given normalized prime constructs the exact comparison on
every element of the original source DVR, through its specified map. -/
theorem actual_tensor_normalization_source_canonical_regular_orders
    [Module.Finite C₀ E] (q : PrimeSpectrum N₀)
    (hheight : (Q₀ q).asIdeal.height = 1) :
    CanonicalRegularSourceOrderComparison (Q₀ q).asIdeal q.asIdeal
      (extendedClosedGaussTensorNormalizationSourceHom H I E s)
      (extendedClosedGaussTensorNormalizationSourcePrime_asIdeal H I E s q) := by
  let : Algebra R₀ S₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ T₀ :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := S₀) (E := E)
  let : Algebra R₀ N₀ := ((algebraMap T₀ N₀).comp (algebraMap R₀ T₀)).toAlgebra
  let Q := (Q₀ q).asIdeal
  let : Q.IsPrime := inferInstanceAs (Q₀ q).asIdeal.IsPrime
  have hmap : extendedClosedGaussTensorNormalizationSourceHom H I E s = algebraMap R₀ N₀ :=
    RingHom.ext (extendedClosedGaussTensorNormalizationSourceHom_canonical_algebraMap H I E s)
  let hlie : q.asIdeal.LiesOver Q := ⟨by
    change (Q₀ q).asIdeal = _
    rw [extendedClosedGaussTensorNormalizationSourcePrime_asIdeal, hmap]
    ⟩
  have hregular := actual_projective_given_prime_canonical_regular_orders H I s hH e Q hheight E
  have h := @hregular q.asIdeal inferInstance hlie
  simpa only [hmap] using h

end DimensionFourDependence
