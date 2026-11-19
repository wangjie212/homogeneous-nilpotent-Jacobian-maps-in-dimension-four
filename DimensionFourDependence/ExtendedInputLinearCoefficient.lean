import DimensionFourDependence.ExtendedNativeSectionGerms
import DimensionFourDependence.ExtendedProductPowerMultiplicity

/-! # The actual input linear section has its original tensor-coordinate coefficient -/

namespace DimensionFourDependence

open AlgebraicGeometry
open scoped TensorProduct

/-- Restoring the omitted projective coordinate gives all four
original coordinate ratios, including the frame coordinate itself. -/
theorem projective_option_elim_ratios
    {F : Type*} [Field F] (x : Fin 4 → F) (s : Fin 4 ≃ Option (Fin 3))
    (hframe : x (s.symm none) ≠ 0) (i : Fin 4) :
    (s i).elim 1 (fun j => x (s.symm (some j)) / x (s.symm none)) =
      x i / x (s.symm none) := by
  have h : (s i).elim 1 (fun j => x (s.symm (some j)) / x (s.symm none)) =
      x (s.symm (s i)) / x (s.symm none) := by
    cases hs : s i <;> simp [div_self hframe]
  exact h.trans (congrArg (fun j => x j / x (s.symm none)) (s.symm_apply_apply i))

/-- A homomorphism retaining the three actual coordinate ratios
retains every original linear-form coefficient in the same frame. -/
theorem linear_form_option_coefficient_value
    {E A F : Type*} [Field E] [CommRing A] [Field F] [Algebra E A] [Algebra E F]
    (φ : A →ₐ[E] F) (c : Fin 3 → A) (x : Fin 4 → F) (s : Fin 4 ≃ Option (Fin 3))
    (hframe : x (s.symm none) ≠ 0)
    (hcoords : ∀ j, φ (c j) = x (s.symm (some j)) / x (s.symm none)) (ν : Fin 4 → E) :
    φ (∑ i, algebraMap E A (ν i) * (s i).elim 1 c) =
      (∑ i, algebraMap E F (ν i) * x i) / x (s.symm none) := by
  rw [map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, φ.commutes]
  have hi : φ ((s i).elim 1 c) = (s i).elim 1
      (fun j => x (s.symm (some j)) / x (s.symm none)) := by
    cases hs : s i <;> simp [hcoords]
  rw [hi, projective_option_elim_ratios x s hframe]
  ring

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

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
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e

local instance extendedInputLinearCoefficientIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedInputLinearCoefficientDomain (a : Fin 4) : IsDomain (T₀ a) :=
  original_tensor_pencil_chart_isDomain H I E (finSuccEquiv' a)
local instance extendedInputLinearCoefficientNonempty (a : Fin 4) : Nonempty (V a) :=
  extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e (finSuccEquiv' a)
noncomputable local instance extendedInputLinearCoefficientAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The native input linear section's actual regular coefficient,
in the canonical normalization ring, is the original linear polynomial
in the original tensor coordinates. -/
theorem extendedClosedGaussInputLinearSection_normalized_coefficient
    (ν : Fin 4 → E) (a : Fin 4) :
    extendedClosedGaussNormalizedChartSectionEquiv H I E hH e (finSuccEquiv' a)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussInputLinearSection H I E hH e ν) a) =
      algebraMap (T₀ a) (normalizationRing (T₀ a))
        (∑ i, algebraMap E (T₀ a) (ν i) *
          (finSuccEquiv' a i).elim 1 (originalTensorPencilCoordinate H I E (finSuccEquiv' a))) := by
  let b := extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e (finSuccEquiv' a)
  apply Subtype.ext
  apply b.injective
  have hval := linear_form_option_coefficient_value
    (extendedClosedGaussTensorChartToOwnFunctionFieldAlgHom H I E hH e (finSuccEquiv' a))
    (originalTensorPencilCoordinate H I E (finSuccEquiv' a)) w (finSuccEquiv' a)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e _)
    (extendedClosedGaussTensorChartToOwnFunctionField_original_coordinate H I E hH e (finSuccEquiv' a)) ν
  have hbridge (t : T₀ a) :
      extendedClosedGaussTensorChartToOwnFunctionFieldAlgHom H I E hH e (finSuccEquiv' a) t =
        b (algebraMap (T₀ a) (FractionRing (T₀ a)) t) := rfl
  have hval' := hval.trans (congrArg
    (fun i : Fin 4 => (∑ j, algebraMap E (N).functionField (ν j) * w j) / w i)
    (finSuccEquiv'_symm_none a))
  have hsection := extendedClosedGaussNormalizedChartFunctionFieldEquiv_section H I E hH e
    (finSuccEquiv' a) (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
      (extendedClosedGaussInputLinearSection H I E hH e ν) a)
  have hgeneric := rationalFrameGlobalCoefficient_generic_value N (fun a : Fin 4 => V a) w
    (extendedClosedGaussNormalizationChartOpen_iSup H I E hH e)
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e)
    (extendedClosedGaussInputLinearSection H I E hH e ν) a
  exact hsection.trans (hgeneric.trans
    ((congrArg (fun v : (N).functionField => v / w a)
      (extendedClosedGaussInputLinearSection_value H I E hH e ν)).trans
        (by
          change _ = b (algebraMap (T₀ a) (FractionRing (T₀ a)) _)
          exact hval'.symm.trans (hbridge _))))

end DimensionFourDependence
