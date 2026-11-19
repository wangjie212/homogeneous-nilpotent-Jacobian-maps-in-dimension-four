import DimensionFourDependence.OriginalSourceCanonicalOrders
import DimensionFourDependence.ProjectiveCanonicalRationalOrders
import DimensionFourDependence.CanonicalLocalMapCongruence

/-! # Canonical rational orders for the specified original source map

The original contracted prime, retained with its primality, gives the
canonical rational comparison for that same specified source homomorphism.
-/

namespace DimensionFourDependence

open AlgebraicGeometry
open scoped TensorProduct

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
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K) x₀ (s.symm none)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N₀" => normalizationRing T₀
local notation "L₀" => projectiveCoordinateChartField (C := K) x₀ (s.symm none)
local notation "Q₀" q:max => extendedClosedGaussTensorNormalizationSourcePrime H I E s q

include hH e in
/-- The specified original source local map has its canonical rational
extension and unchanged normalized valuations at the given normalized prime. -/
theorem actual_tensor_normalization_source_canonical_rational_orders
    [Module.Finite C₀ E] (q : PrimeSpectrum N₀) (hheight : (Q₀ q).asIdeal.height = 1) :
    letI : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
    letI : IsDomain T₀ := subalgebra_algebraic_base_change_isDomain
      (L := E) (closedGaussParameterField_relatively_closed H I) S₀
    letI : IsDiscreteValuationRing (Localization.AtPrime (Q₀ q).asIdeal) :=
      projective_source_height_one_isDVR s (Q₀ q).asIdeal hheight
    letI : Algebra (Localization.AtPrime (Q₀ q).asIdeal) L₀ := primeLocalizationFractionAlgebra (Q₀ q).asIdeal
    letI : IsFractionRing (Localization.AtPrime (Q₀ q).asIdeal) L₀ := projective_source_divisor_isFractionRing s (Q₀ q).asIdeal
    CanonicalRationalSourceOrderComparison
      (O := Localization.AtPrime (Q₀ q).asIdeal) (A := Localization.AtPrime q.asIdeal) (F := L₀)
      (Localization.localRingHom (Q₀ q).asIdeal q.asIdeal
        (extendedClosedGaussTensorNormalizationSourceHom H I E s)
        (extendedClosedGaussTensorNormalizationSourcePrime_asIdeal H I E s q)) := by
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : IsDomain T₀ := subalgebra_algebraic_base_change_isDomain
    (L := E) (closedGaussParameterField_relatively_closed H I) S₀
  let : IsDiscreteValuationRing (Localization.AtPrime (Q₀ q).asIdeal) :=
    projective_source_height_one_isDVR s (Q₀ q).asIdeal hheight
  let : Algebra (Localization.AtPrime (Q₀ q).asIdeal) L₀ := primeLocalizationFractionAlgebra (Q₀ q).asIdeal
  let : IsFractionRing (Localization.AtPrime (Q₀ q).asIdeal) L₀ := projective_source_divisor_isFractionRing s (Q₀ q).asIdeal
  let : Algebra R₀ S₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ T₀ := sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := S₀) (E := E)
  let : Algebra R₀ N₀ := ((algebraMap T₀ N₀).comp (algebraMap R₀ T₀)).toAlgebra
  let Q := (Q₀ q).asIdeal
  let : Q.IsPrime := inferInstanceAs (Q₀ q).asIdeal.IsPrime
  have hmap : extendedClosedGaussTensorNormalizationSourceHom H I E s = algebraMap R₀ N₀ :=
    RingHom.ext (extendedClosedGaussTensorNormalizationSourceHom_canonical_algebraMap H I E s)
  let hlie : q.asIdeal.LiesOver Q := ⟨by
    change (Q₀ q).asIdeal = _
    rw [extendedClosedGaussTensorNormalizationSourcePrime_asIdeal, hmap]⟩
  have hcomparison := actual_projective_given_prime_canonical_rational_orders H I s hH e Q hheight E
  have h := @hcomparison q.asIdeal inferInstance hlie
  have hlocal := canonical_localRingHom_congr Q q.asIdeal
    (extendedClosedGaussTensorNormalizationSourceHom H I E s) (algebraMap R₀ N₀)
    (extendedClosedGaussTensorNormalizationSourcePrime_asIdeal H I E s q) hlie.over hmap
  rw [hlocal]
  exact h

end DimensionFourDependence
