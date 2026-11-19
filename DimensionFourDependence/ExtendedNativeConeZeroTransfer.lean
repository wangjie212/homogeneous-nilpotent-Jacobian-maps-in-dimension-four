import DimensionFourDependence.ExtendedNativeConeRoots
import DimensionFourDependence.NormalizationConeChartObstruction
import DimensionFourDependence.UnitSectionCoefficientInverseIntegral

/-! # An actual nonvertex cone zero constructs a zero divisor on the original projective normalization -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
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
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "s₀" => finSuccEquiv' (0 : Fin 4)
local notation "x₀" => (fun i : Fin 3 => w ((s₀).symm (some i)))
local notation "g₀" => extendedClosedGaussNormalization_original_affine_field_top H I E hH e
local notation "A₀" => extendedClosedGaussNativeConeAlgebra H I E hH e
local notation "B₀" => normalizationRing A₀
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E

local instance extendedNativeConeZeroTransferIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedNativeConeZeroTransferAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- A nonvertex zero of the actual lifted U makes its corresponding
actual original-frame section coefficient a nonunit. The inverse regular
coefficient would be integral in the cone prime-local chart and force
the nonvanishing original coordinate into that same prime. -/
theorem actual_native_cone_root_zero_forces_nonunit_original_coefficient
    (ν c : Fin 4 → E) (r : (N).functionField) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E c)) (α β : E)
    (hu : extendedClosedGaussHyperplaneGlobalValue H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β) ≠ 0)
    (Q : Ideal B₀) [Q.IsPrime]
    (hb : extendedClosedGaussNativeConeRootCombination H I E hH e ν c r hd hroot α β ∈ Q)
    (a : Fin 4) (ha : algebraMap A₀ B₀ (extendedClosedGaussNativeConeCoordinate H I E hH e a) ∉ Q) :
    ¬ IsUnit (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β) a) := by
  intro hunit
  let u := extendedClosedGaussHyperplaneGlobalValue H I E hH e
    (extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β)
  let ψ := extendedClosedGaussNativeConeConstantHom H I E hH e
  let z := extendedClosedGaussNativeConeCoordinate H I E hH e
  let t := algebraMap A₀ (FractionRing A₀) (projectiveConeCoordinate (E := E) x₀ none)
  have htvalue : projectiveConeFractionEmbedding (E := E) x₀ t = RatFunc.X := by
    simpa only [Option.elim_none, map_one, one_mul] using
      projectiveConeFractionEmbedding_coordinate (E := E) x₀ none
  have ht : t ≠ 0 := fun hzero => RatFunc.X_ne_zero
    (htvalue.symm.trans ((congrArg (projectiveConeFractionEmbedding (E := E) x₀) hzero).trans
      (map_zero (projectiveConeFractionEmbedding (E := E) x₀))))
  have hratios (i : Fin 4) : ψ (w i / w a) =
      algebraMap A₀ (FractionRing A₀) (z i) / algebraMap A₀ (FractionRing A₀) (z a) :=
    common_radial_coordinate_ratios ψ.toRingHom w (fun i => algebraMap A₀ (FractionRing A₀) (z i)) t ht
      (extendedClosedGaussNativeConeConstantHom_mul_radial_coordinate H I E hH e) a
      (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a) i
  have hp : (extendedClosedGaussNativeConeRootCombination H I E hH e ν c r hd hroot α β : FractionRing A₀) *
      ψ (w a / u) = algebraMap A₀ (FractionRing A₀) (z a) := by
    change projectiveConeRadialLift x₀ g₀ u * projectiveConeFractionConstantHom x₀ g₀ (w a / u) = _
    exact (projectiveConeRadialLift_mul_constant_div x₀ g₀ u (w a) hu).trans
      (extendedClosedGaussNativeConeConstantHom_mul_radial_coordinate H I E hH e a)
  exact normalization_cone_zero_excludes_integral_inverse_chart_coefficient Q ψ w z a
    (extendedClosedGaussNativeConeRootCombination H I E hH e ν c r hd hroot α β) u hb ha hratios hp
    (extendedClosedGauss_unit_section_coefficient_inverse_isIntegral H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β) a hunit)

/-- Every nonzero actual root-combination section on the actual
normalized projective pencil has a constructed actual zero divisor.
The original cone normalization supplies a nonvertex zero, which
constructs a nonunit actual coefficient and then the original chart prime. -/
theorem actual_native_nonzero_root_combination_has_zero_divisor
    (hGauss : gaussImageDimension H I = 1)
    (ν c : Fin 4 → E) (r : (N).functionField) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E c)) (α β : E)
    (hu : extendedClosedGaussHyperplaneGlobalValue H I E hH e
      (extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β) ≠ 0) :
    ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))), q.asIdeal.height = 1 ∧
      Order.coheight (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q) = 1 ∧
      extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β) a q ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q)) := by
  obtain ⟨Q, _hQ, hvan, a, ha⟩ := actual_native_radial_cone_element_has_nonvertex_vanishing_divisor
    H I E hH e hGauss (extendedClosedGaussNativeConeRootCombination H I E hH e ν c r hd hroot α β) _ hu
    (extendedClosedGaussNativeConeRootCombination_value H I E hH e ν c r hd hroot α β)
  have hunit := actual_native_cone_root_zero_forces_nonunit_original_coefficient H I E hH e
    ν c r hd hroot α β hu Q.asIdeal hvan a ha
  have hne : extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β ≠ 0 := by
    intro hzero
    apply hu
    rw [hzero]
    rfl
  obtain ⟨q, hq, hcodim, hqvan⟩ := actual_native_nonunit_section_coefficient_has_zero_divisor H I E hH e
    (extendedClosedGaussRootCombinationSection H I E hH e ν c r hd hroot α β) hne a hunit
  exact ⟨a, q, hq, hcodim, hqvan⟩

/-- The original nonzero root and actual product-power equation
derive nonvanishing and construct the actual zero divisor of U on the
original normalized projective pencil. No vanishing locus is supplied. -/
theorem actual_native_root_combination_has_zero_divisor_of_product_power
    (hGauss : gaussImageDimension H I = 1)
    (ν cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0) (hd : 0 < d)
    (hroot : r ^ d = aeval w (extendedClosedGaussOutputLinearPolynomial H I E cS)) (α β : E)
    (hprod : extendedClosedGaussHyperplaneGlobalValue H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) *
          aeval w (extendedClosedGaussOutputLinearPolynomial H I E cN) = r ^ (d + 1)) :
    ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))), q.asIdeal.height = 1 ∧
      Order.coheight (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q) = 1 ∧
      extendedClosedGaussHyperplaneGlobalCoefficientGerm H I E hH e
        (extendedClosedGaussRootCombinationSection H I E hH e ν cS r hd hroot α β) a q ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk
          (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q)) :=
  actual_native_nonzero_root_combination_has_zero_divisor H I E hH e hGauss ν cS r hd hroot α β
    (mul_ne_zero_iff.mp (hprod ▸ pow_ne_zero (d + 1) hr)).1

end DimensionFourDependence
