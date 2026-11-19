import DimensionFourDependence.ScalarExtendedSourceRelations
import DimensionFourDependence.ExtendedOriginalHomogeneousRelations

/-! # Exact homogeneous source relations in the native normalized pencil field

The actual generic quotient chart maps to the native function field via
the proved tensor-chart identification. It retains all coefficients and
original coordinates. Homogeneous vanishing in the actual extended
source tensor is consequently equivalent to native vanishing.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

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
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "Pₑ" => extendedClosedGaussPencilIdeal H I E
local notation "z" => primeQuotientCoordinate Pₑ
local notation "s₀" => finSuccEquiv' (0 : Fin 4)
local notation "Aₑ" => projectiveCoordinateChartAlgebra (C := E) (z) ((s₀).symm none)
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance nativeHomogeneousSourceRelationsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeHomogeneousSourceRelationsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual generic quotient chart maps into the actual native
scheme function field through the original tensor-chart isomorphism. -/
noncomputable def extendedClosedGaussGenericChartToOwnField : Aₑ →+* (N).functionField :=
  (extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s₀).comp
    (extendedClosedGaussRatioCoordinateEquiv H I E hH e s₀).symm.toRingHom

/-- The actual generic quotient chart retains every extended
coefficient in the native function field. -/
theorem extendedClosedGaussGenericChartToOwnField_coefficient (c : E) :
    extendedClosedGaussGenericChartToOwnField H I E hH e (algebraMap E (Aₑ) c) =
      algebraMap E (N).functionField c := by
  let b := extendedClosedGaussRatioCoordinateEquiv H I E hH e s₀
  change extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s₀
    (b.symm (algebraMap E (Aₑ) c)) = _
  rw [← extendedClosedGaussRatioCoordinateEquiv_tmul_coefficient H I E hH e s₀ c,
    b.symm_apply_apply]
  exact extendedClosedGaussTensorChartToOwnFunctionField_coefficient H I E hH e s₀ c

/-- The actual generic quotient chart retains every original
coordinate as the corresponding native weight. -/
theorem extendedClosedGaussGenericChartToOwnField_coordinate (i : Fin 4) :
    extendedClosedGaussGenericChartToOwnField H I E hH e
      (projectiveChartTransition (C := E) (z) ((s₀).symm none) i) = (w) i := by
  change extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s₀
    ((extendedClosedGaussRatioCoordinateEquiv H I E hH e s₀).symm
      (projectiveChartTransition (C := E) (z) ((s₀).symm none) i)) = (w) i
  simpa only [finSuccEquiv'_symm_none, extendedClosedGaussNormalizationHyperplaneWeight_zero, div_one] using
    extendedClosedGaussTensorChartToOwnFunctionField_coordinate_weight H I E hH e s₀ i

/-- The actual chart comparison retains the value of every
polynomial over the full algebraic coefficient extension. -/
theorem extendedClosedGaussGenericChartToOwnField_polynomial_value
    (P : MvPolynomial (Fin 4) E) :
    extendedClosedGaussGenericChartToOwnField H I E hH e
      (aeval (fun i => projectiveChartTransition (C := E) (z) ((s₀).symm none) i) P) = aeval (w) P := by
  have heq : (extendedClosedGaussGenericChartToOwnField H I E hH e).comp
      (aeval (fun i => projectiveChartTransition (C := E) (z) ((s₀).symm none) i)).toRingHom =
        (aeval (R := E) (w)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      exact extendedClosedGaussGenericChartToOwnField_coefficient H I E hH e c
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      exact extendedClosedGaussGenericChartToOwnField_coordinate H I E hH e i
  exact RingHom.congr_fun heq P

/-- The native generic chart comparison is injective. -/
theorem extendedClosedGaussGenericChartToOwnField_injective :
    Function.Injective (extendedClosedGaussGenericChartToOwnField H I E hH e) :=
  (extendedClosedGaussTensorChartToOwnFunctionField_injective H I E hH e s₀).comp
    (extendedClosedGaussRatioCoordinateEquiv H I E hH e s₀).symm.injective

/-- A homogeneous polynomial over the full algebraic coefficient
extension vanishes natively exactly when it belongs to the actual
extended original source ideal. Both vanishing and nonvanishing transfer. -/
theorem extendedClosedGauss_native_homogeneous_zero_iff
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n) :
    aeval (w) P = 0 ↔ P ∈ Pₑ := by
  let A := Aₑ
  let q := aeval (fun i => projectiveChartTransition (C := E) (z) ((s₀).symm none) i) P
  have hq : q = 0 ↔ aeval (fun i => (z) i / (z) ((s₀).symm none)) P = 0 := by
    have he := comp_aeval_apply
      (fun i => projectiveChartTransition (C := E) (z) ((s₀).symm none) i) A.val P
    change A.val q = aeval (fun i => (z) i / (z) ((s₀).symm none)) P at he
    rw [← he]
    exact (map_eq_zero_iff _ (show Function.Injective A.val from Subtype.val_injective)).symm
  have hscale : aeval (fun i => (z) i / (z) ((s₀).symm none)) P =
      ((z) ((s₀).symm none))⁻¹ ^ n * aeval (z) P := by
    simpa only [div_eq_mul_inv, mul_comm] using
      homogeneous_aeval_scale_indexed P hP (z) ((z) ((s₀).symm none))⁻¹
  have hnz : ((z) ((s₀).symm none))⁻¹ ^ n ≠ 0 :=
    pow_ne_zero n (inv_ne_zero (extendedClosedGaussRatioCoordinate_ne_zero H I E _))
  have hnative : aeval (w) P = 0 ↔ q = 0 := by
    rw [← extendedClosedGaussGenericChartToOwnField_polynomial_value H I E hH e P]
    exact map_eq_zero_iff _ (extendedClosedGaussGenericChartToOwnField_injective H I E hH e)
  rw [hnative, hq, hscale, mul_eq_zero, or_iff_right hnz]
  change P ∈ RingHom.ker (aeval (z)).toRingHom ↔ P ∈ Pₑ
  rw [extendedClosedGaussRatioCoordinate_relations]

/-- Every homogeneous identity in the actual source tensor holds
in the actual normalized pencil field, and conversely. -/
theorem extendedClosedGauss_source_tensor_native_homogeneous_zero_iff
    (P : MvPolynomial (Fin 4) E) {n : ℕ} (hP : P.IsHomogeneous n) :
    aeval (extendedClosedGaussSourceTensorCoordinate H I E) P = 0 ↔ aeval (w) P = 0 :=
  (extendedClosedGaussSourceTensorCoordinate_zero_iff H I E P).trans
    (extendedClosedGauss_native_homogeneous_zero_iff H I E hH e P hP).symm

end DimensionFourDependence
