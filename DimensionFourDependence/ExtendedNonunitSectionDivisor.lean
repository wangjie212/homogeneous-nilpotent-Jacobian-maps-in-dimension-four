import DimensionFourDependence.PrincipalVanishingDivisor
import DimensionFourDependence.ExtendedInputLinearResidue
import DimensionFourDependence.AffineStalkDimension

/-! # A nonunit actual section coefficient constructs an actual zero divisor -/

namespace DimensionFourDependence

open AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" s:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm s none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "M" => extendedClosedGaussNormalizationHyperplaneModuleSheaf H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)

local instance extendedNonunitSectionDivisorIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e

/-- Every original tensor normalization chart has its actual
Noetherian ring, derived from the original finite-type coefficient algebra. -/
theorem original_tensor_pencil_normalization_chart_isNoetherian
    (s : Fin 4 ≃ Option (Fin 3)) : IsNoetherianRing (normalizationRing (T₀ s)) := by
  let : IsDomain (T₀ s) := original_tensor_pencil_chart_isDomain H I E s
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  let : Algebra.FiniteType C₀ (closedGaussPencilChartAlgebra H I s) :=
    closedGaussPencilChartAlgebra_finiteType H I s
  let φ := originalTensorPencilCoordinateEquiv H I E s
  let : Algebra.FiniteType E (T₀ s) := (inferInstance : Algebra.FiniteType E
    (E ⊗[C₀] closedGaussPencilChartAlgebra H I s)).equiv φ.symm
  exact normalizationRing_isNoetherianRing (T₀ s) (K := E)

/-- The actual tensor prime has exactly the intrinsic codimension
of its actual global normalization point. -/
theorem extendedClosedGaussNormalizationTensorChartPoint_coheight_eq_height
    (s : Fin 4 ≃ Option (Fin 3)) (q : PrimeSpectrum (normalizationRing (T₀ s))) :
    Order.coheight (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q) = q.asIdeal.height := by
  have h := ringKrullDim_eq_of_ringEquiv
    (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q)
  rw [ringKrullDim_stalk_eq_coheight,
    IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal)] at h
  exact_mod_cast h

/-- A nonunit coefficient of a nonzero actual global section
constructs an actual height-one zero prime and an intrinsic zero divisor
on the normalization. Neither the prime nor a divisor is given. -/
theorem actual_native_nonunit_section_coefficient_has_zero_divisor
    (s : Γ(M, ⊤)) (hs : s ≠ 0) (a : Fin 4)
    (hu : ¬ IsUnit (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a)) :
    ∃ q : PrimeSpectrum (normalizationRing (T₀ (finSuccEquiv' a))),
      q.asIdeal.height = 1 ∧
      Order.coheight (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q) = 1 ∧
      extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e s a q ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q)) := by
  let : IsDomain (T₀ (finSuccEquiv' a)) := original_tensor_pencil_chart_isDomain H I E (finSuccEquiv' a)
  let : IsNoetherianRing (normalizationRing (T₀ (finSuccEquiv' a))) :=
    original_tensor_pencil_normalization_chart_isNoetherian H I E (finSuccEquiv' a)
  let φ := extendedClosedGaussNormalizedChartSectionEquiv H I E hH e (finSuccEquiv' a)
  let f := extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a
  have hf : f ≠ 0 := extendedClosedGaussHyperplaneGlobalCoefficient_ne_zero H I E hH e s hs a
  have hφ : φ f ≠ 0 := fun h => hf (φ.injective (h.trans (map_zero φ).symm))
  have hunit : ¬ IsUnit (φ f) := fun h => hu (by
    simpa only [RingEquiv.symm_apply_apply] using h.map φ.symm)
  obtain ⟨q, hq, hmem⟩ := nonzero_nonunit_function_has_vanishing_divisor (φ f) hφ hunit
  exact ⟨q, hq,
    (extendedClosedGaussNormalizationTensorChartPoint_coheight_eq_height H I E hH e (finSuccEquiv' a) q).trans hq,
    (extendedClosedGaussNormalizedChartSection_mem_prime_iff_germ H I E hH e (finSuccEquiv' a) q f).mp hmem⟩

/-- A nonzero actual section has an invertible chart coefficient
exactly when that chart has no actual divisor where the section vanishes. -/
theorem actual_native_section_coefficient_isUnit_iff_no_zero_divisor
    (s : Γ(M, ⊤)) (hs : s ≠ 0) (a : Fin 4) :
    IsUnit (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e s a) ↔
      ∀ q : PrimeSpectrum (normalizationRing (T₀ (finSuccEquiv' a))), q.asIdeal.height = 1 →
        extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e s a q ∉
          IsLocalRing.maximalIdeal ((N).presheaf.stalk
            (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q)) := by
  constructor
  · intro hu q _
    exact IsLocalRing.notMem_maximalIdeal.mpr (hu.map ((N).presheaf.germ (V a) _
      (extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q)).hom)
  · intro h
    by_contra hu
    obtain ⟨q, hq, _hcodim, hvan⟩ := actual_native_nonunit_section_coefficient_has_zero_divisor
      H I E hH e s hs a hu
    exact h q hq hvan

end DimensionFourDependence
