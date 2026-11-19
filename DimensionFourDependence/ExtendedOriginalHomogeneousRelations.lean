import DimensionFourDependence.ExtendedHomogeneousPowerSections
import DimensionFourDependence.ExtendedOwnCoordinateCharts

/-! # Original homogeneous relations survive in the native normalized pencil field -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "s₀" => finSuccEquiv' (0 : Fin 4)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ ((s₀).symm none)
local notation "T₀" => S₀ ⊗[C₀] E

local instance extendedOriginalHomogeneousRelationsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedOriginalHomogeneousRelationsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The original frame X0/X0 is the unit in the actual native field. -/
theorem extendedClosedGaussNormalizationHyperplaneWeight_zero : w 0 = 1 :=
  projectivePullbackRationalCoordinate_self N
    (extendedClosedGaussNormalizationProjectiveMap H I E hH e)
    (extendedClosedGaussNormalizationProjectiveMap_chart_nonempty H I E hH e) 0

/-- The original closed-parameter coordinate chart maps into the
actual native field through its actual tensor coefficient extension. -/
noncomputable def extendedClosedGaussOriginalChartToOwnField : S₀ →+* (N).functionField :=
  (extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s₀).comp
    Algebra.TensorProduct.includeLeftRingHom

/-- The original closed-parameter scalar has its specified extended
coefficient value under the actual chart embedding. -/
theorem extendedClosedGaussOriginalChartToOwnField_coefficient (c : C₀) :
    extendedClosedGaussOriginalChartToOwnField H I E hH e (algebraMap C₀ S₀ c) =
      algebraMap E (N).functionField (algebraMap C₀ E c) := by
  change extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s₀
    (algebraMap C₀ S₀ c ⊗ₜ[C₀] (1 : E)) = _
  rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
  exact extendedClosedGaussTensorChartToOwnFunctionField_coefficient H I E hH e s₀ _

/-- Original coordinate-ratio values map to the actual native frame
weights, with the same original four coordinate labels. -/
theorem extendedClosedGaussOriginalChartToOwnField_coordinate (i : Fin 4) :
    extendedClosedGaussOriginalChartToOwnField H I E hH e
      (projectiveChartTransition (C := C₀) x₀ ((s₀).symm none) i) = w i := by
  let b := extendedClosedGaussRatioCoordinateEquiv H I E hH e s₀
  have ht : projectiveChartTransition (C := C₀) x₀ ((s₀).symm none) i ⊗ₜ[C₀] (1 : E) =
      b.symm (projectiveChartTransition (C := E)
        (primeQuotientCoordinate (extendedClosedGaussPencilIdeal H I E)) ((s₀).symm none) i) := by
    apply b.injective
    exact (extendedClosedGaussRatioCoordinateEquiv_tmul_ratio H I E hH e s₀ i).trans
      (b.apply_symm_apply _).symm
  have hv := extendedClosedGaussTensorChartToOwnFunctionField_coordinate_weight H I E hH e s₀ i
  change extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s₀
    (projectiveChartTransition (C := C₀) x₀ ((s₀).symm none) i ⊗ₜ[C₀] (1 : E)) = _
  rw [ht]
  simpa only [finSuccEquiv'_symm_none, extendedClosedGaussNormalizationHyperplaneWeight_zero,
    div_one] using hv

/-- Evaluation of every original closed-parameter polynomial at the
actual original ratios agrees with native evaluation after coefficient
extension; no polynomial relation is lost in this comparison. -/
theorem extendedClosedGaussOriginalChartToOwnField_polynomial_value
    (P : MvPolynomial (Fin 4) C₀) :
    extendedClosedGaussOriginalChartToOwnField H I E hH e
      (aeval (fun i => projectiveChartTransition (C := C₀) x₀ ((s₀).symm none) i) P) =
        aeval w (MvPolynomial.map (algebraMap C₀ E) P) := by
  have heq : (extendedClosedGaussOriginalChartToOwnField H I E hH e).comp
      (aeval (fun i => projectiveChartTransition (C := C₀) x₀ ((s₀).symm none) i)).toRingHom =
    (aeval w).toRingHom.comp (MvPolynomial.map (algebraMap C₀ E)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        aeval_C, MvPolynomial.map_C]
      exact extendedClosedGaussOriginalChartToOwnField_coefficient H I E hH e c
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        aeval_X, MvPolynomial.map_X]
      exact extendedClosedGaussOriginalChartToOwnField_coordinate H I E hH e i
  exact RingHom.congr_fun heq P

/-- Every original homogeneous source relation over the actual
closed Gauss parameter field remains a relation at the native pencil's
actual original projective weights after algebraic coefficient extension. -/
theorem extendedClosedGauss_original_homogeneous_relation
    (P : MvPolynomial (Fin 4) C₀) {n : ℕ} (hP : P.IsHomogeneous n)
    (hzero : aeval x₀ P = 0) : aeval w (MvPolynomial.map (algebraMap C₀ E) P) = 0 := by
  have hnormalized : aeval (fun i => x₀ i / x₀ ((s₀).symm none)) P = 0 := by
    have hs := homogeneous_aeval_scale_indexed P hP x₀ (x₀ ((s₀).symm none))⁻¹
    simpa only [div_eq_mul_inv, mul_comm, hzero, mul_zero, zero_mul] using hs
  have hchart : aeval (fun i => projectiveChartTransition (C := C₀) x₀ ((s₀).symm none) i) P = 0 := by
    apply Subtype.val_injective
    exact (MvPolynomial.comp_aeval_apply
      (fun i => projectiveChartTransition (C := C₀) x₀ ((s₀).symm none) i) (S₀).val P).trans hnormalized
  have hv := extendedClosedGaussOriginalChartToOwnField_polynomial_value H I E hH e P
  rw [hchart, map_zero] at hv
  exact hv.symm

end DimensionFourDependence
