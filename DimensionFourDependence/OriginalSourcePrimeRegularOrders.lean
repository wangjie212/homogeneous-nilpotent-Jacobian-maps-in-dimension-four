import DimensionFourDependence.GlobalNormalizationMultiplicity
import DimensionFourDependence.ProjectiveCanonicalRegularOrders

/-! # Exact regular orders at the original contracted tensor prime

This local calculation uses the specified original source homomorphism,
before transporting it through any global geometric stalk isomorphism.
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

omit [CharZero K] [Algebra.IsAlgebraic C₀ E] in
/-- The original source point of a tensor-normalization prime, retaining
its primality without expanding the coefficient-extension field data. -/
@[irreducible] noncomputable def extendedClosedGaussTensorNormalizationSourcePrime
    (q : PrimeSpectrum N₀) : PrimeSpectrum R₀ :=
  PrimeSpectrum.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s) q

omit [CharZero K] [Algebra.IsAlgebraic C₀ E] in
/-- The specified source point has exactly the original contracted ideal. -/
theorem extendedClosedGaussTensorNormalizationSourcePrime_asIdeal
    (q : PrimeSpectrum N₀) :
    (extendedClosedGaussTensorNormalizationSourcePrime H I E s q).asIdeal =
      q.asIdeal.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s) := by
  unfold extendedClosedGaussTensorNormalizationSourcePrime
  rfl

local notation "Q₀" q:max => PrimeSpectrum.asIdeal
  (extendedClosedGaussTensorNormalizationSourcePrime H I E s q)

include hH e in
/-- The specified original source map preserves every regular order
bound at a given tensor-normalization prime with height-one contraction. -/
theorem actual_tensor_normalization_source_regular_order_iff
    [Module.Finite C₀ E] (q : PrimeSpectrum N₀)
    (hheight : (Q₀ q).height = 1) (r : R₀) (a : ℕ) :
    algebraMap N₀ (Localization.AtPrime q.asIdeal)
        (extendedClosedGaussTensorNormalizationSourceHom H I E s r) ∈
          (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) ^ a ↔
      algebraMap R₀ (Localization.AtPrime (Q₀ q)) r ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime (Q₀ q))) ^ a := by
  let : Algebra R₀ S₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ T₀ :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := S₀) (E := E)
  let : Algebra R₀ N₀ := ((algebraMap T₀ N₀).comp (algebraMap R₀ T₀)).toAlgebra
  let Q := Q₀ q
  let : Q.IsPrime := inferInstanceAs (Q₀ q).IsPrime
  let hlie : q.asIdeal.LiesOver Q := ⟨by
    change (extendedClosedGaussTensorNormalizationSourcePrime H I E s q).asIdeal = _
    rw [extendedClosedGaussTensorNormalizationSourcePrime_asIdeal]
    rfl⟩
  have hregular := actual_projective_given_prime_canonical_regular_orders H I s hH e Q hheight E
  have h := @hregular q.asIdeal inferInstance hlie
  change algebraMap N₀ (Localization.AtPrime q.asIdeal) (algebraMap R₀ N₀ r) ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) ^ a ↔ _
  exact canonicalRegularSourceOrderComparison_algebraMap Q q.asIdeal (algebraMap R₀ N₀)
    hlie.over h r a

end DimensionFourDependence
