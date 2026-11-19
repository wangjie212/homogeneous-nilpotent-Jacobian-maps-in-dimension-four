import DimensionFourDependence.ExtendedGaussSourceCoordinates

/-! # Normalized extended source charts retain the original source prime

The original chart is a polynomial algebra in its three actual ratios.
Its independent evaluation map to the extended generic-point chart
agrees with the original tensor inclusion. Normalization preserves this
commutative square, so corresponding primes have the same original
source contraction.
-/

namespace DimensionFourDependence

open scoped TensorProduct

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- An isomorphism commuting with specified source maps preserves the
contraction of every ideal to that same source. -/
theorem sourceCompatibleRingEquiv_ideal_contraction
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (b : A ≃+* B) (f : R →+* A) (g : R →+* B)
    (h : ∀ r, b (f r) = g r) (q : Ideal A) :
    (q.map b.toRingHom).comap g = q.comap f := by
  have hmap : g = b.toRingHom.comp f := RingHom.ext (fun r => (h r).symm)
  rw [hmap, ← Ideal.comap_comap, Ideal.comap_map_of_bijective b.toRingHom b.bijective]

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "zₑ" => primeQuotientCoordinate (extendedClosedGaussPencilIdeal H I E)
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K) x₀ (s.symm none)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "Sₑ" => projectiveCoordinateChartAlgebra (C := E) zₑ (s.symm none)

/-- Evaluation of every original source-chart function at the actual
extended coordinate ratios, using its unique polynomial expression. -/
noncomputable def extendedClosedGaussSourceChartHom : R₀ →+* Sₑ :=
  (extendedClosedGaussSourcePolynomialHom H I E s).comp
    (projectiveSourceFullChartCoordinateEquiv (K := K) s).symm.toRingHom

/-- The independent actual-source evaluation agrees on the entire
original source chart with the specified original tensor inclusion. -/
theorem extendedClosedGaussSourceChartHom_compatibility (r : R₀) :
    extendedClosedGaussRatioCoordinateEquiv H I E hH e s
      (extendedClosedGaussTensorSourceHom H I E s r) =
      extendedClosedGaussSourceChartHom H I E s r := by
  have h := extendedClosedGaussTensorSourceHom_polynomial H I E hH e s
    ((projectiveSourceFullChartCoordinateEquiv (K := K) s).symm r)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h

/-- The original source action on the canonical tensor normalization. -/
noncomputable def extendedClosedGaussTensorNormalizationSourceHom :
    R₀ →+* normalizationRing (S₀ ⊗[C₀] E) :=
  (algebraMap (S₀ ⊗[C₀] E) (normalizationRing (S₀ ⊗[C₀] E))).comp
    (extendedClosedGaussTensorSourceHom H I E s)

/-- The original source action on the actual normalized extended ratio
chart is defined by the actual extended source ratios. -/
noncomputable def extendedClosedGaussRatioNormalizationSourceHom :
    R₀ →+* normalizationRing Sₑ :=
  (algebraMap Sₑ (normalizationRing Sₑ)).comp
    (extendedClosedGaussSourceChartHom H I E s)

/-- The normalized coordinate isomorphism preserves every original
source function through its actual ratio evaluation. -/
theorem extendedClosedGaussNormalizedSource_compatibility (r : R₀) :
    extendedClosedGaussNormalizedRatioCoordinateEquiv H I E hH e s
      (extendedClosedGaussTensorNormalizationSourceHom H I E s r) =
      extendedClosedGaussRatioNormalizationSourceHom H I E s r := by
  change extendedClosedGaussNormalizedRatioCoordinateEquiv H I E hH e s
    (algebraMap (S₀ ⊗[C₀] E) (normalizationRing (S₀ ⊗[C₀] E))
      (extendedClosedGaussTensorSourceHom H I E s r)) = _
  rw [extendedClosedGaussNormalizedRatioCoordinateEquiv_algebraMap,
    extendedClosedGaussSourceChartHom_compatibility]
  rfl

/-- Corresponding normalized extended chart ideals have exactly the
same contraction to the original source chart. -/
theorem extendedClosedGaussNormalizedSource_prime_contraction
    (q : Ideal (normalizationRing (S₀ ⊗[C₀] E))) :
    (q.map (extendedClosedGaussNormalizedRatioCoordinateEquiv H I E hH e s).toRingHom).comap
        (extendedClosedGaussRatioNormalizationSourceHom H I E s) =
      q.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s) := by
  exact sourceCompatibleRingEquiv_ideal_contraction
    (extendedClosedGaussNormalizedRatioCoordinateEquiv H I E hH e s)
    (extendedClosedGaussTensorNormalizationSourceHom H I E s)
    (extendedClosedGaussRatioNormalizationSourceHom H I E s)
    (extendedClosedGaussNormalizedSource_compatibility H I E hH e s) q

/-- A prime over a specified original source divisor remains over that
same divisor in the actual normalized extended ratio chart. -/
theorem extendedClosedGaussNormalizedSource_prime_over_iff
    (q : Ideal (normalizationRing (S₀ ⊗[C₀] E))) (Q : Ideal R₀) :
    (q.map (extendedClosedGaussNormalizedRatioCoordinateEquiv H I E hH e s).toRingHom).comap
        (extendedClosedGaussRatioNormalizationSourceHom H I E s) = Q ↔
      q.comap (extendedClosedGaussTensorNormalizationSourceHom H I E s) = Q := by
  rw [extendedClosedGaussNormalizedSource_prime_contraction]

end DimensionFourDependence
