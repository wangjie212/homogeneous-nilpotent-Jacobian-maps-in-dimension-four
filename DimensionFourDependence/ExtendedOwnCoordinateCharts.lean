import DimensionFourDependence.ExtendedNormalizedCoefficientValues
import DimensionFourDependence.ProjectiveChartThreeGenerators

/-! # Original tensor coordinate rings are the native frame-ratio algebras -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
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
local notation "T₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "Uₙ" => extendedClosedGaussNormalizationChartOpen H I E hH e s

local instance extendedOwnCoordinateChartsIntegral : IsIntegral N := extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedOwnCoordinateChartsDomain : IsDomain T₀ := original_tensor_pencil_chart_isDomain H I E s
local instance extendedOwnCoordinateChartsNonempty : Nonempty Uₙ := extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e s
noncomputable local instance extendedOwnCoordinateChartsAlgebra : Algebra E (N).functionField := extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The original three free tensor ratios are exactly the native
original frame ratios in the normalized scheme's own function field. -/
theorem extendedClosedGaussTensorChartToOwnFunctionField_original_coordinate (i : Fin 3) :
    extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s
        (originalTensorPencilCoordinate H I E s i) =
      w (s.symm (some i)) / w (s.symm none) := by
  let b := extendedClosedGaussRatioCoordinateEquiv H I E hH e s
  have heq : originalTensorPencilCoordinate H I E s i = b.symm
      (projectiveChartTransition (C := E)
        (primeQuotientCoordinate (extendedClosedGaussPencilIdeal H I E))
        (s.symm none) (s.symm (some i))) := by
    apply b.injective
    exact (extendedClosedGaussRatioCoordinateEquiv_tmul_ratio H I E hH e s
      (s.symm (some i))).trans (b.apply_symm_apply _).symm
  exact (congrArg (extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s) heq).trans
    (extendedClosedGaussTensorChartToOwnFunctionField_coordinate_weight H I E hH e s
      (s.symm (some i)))

/-- The image of the entire original tensor chart is exactly the
native original-frame ratio algebra, with the same extended coefficients. -/
theorem extendedClosedGaussTensorChartToOwnFunctionField_range :
    (extendedClosedGaussTensorChartToOwnFunctionFieldAlgHom H I E hH e s).range =
      projectiveCoordinateChartAlgebra (C := E) w (s.symm none) := by
  let φ := extendedClosedGaussTensorChartToOwnFunctionFieldAlgHom H I E hH e s
  have h := congrArg (Subalgebra.map φ) (originalTensorPencilCoordinate_adjoin H I E s)
  rw [AlgHom.map_adjoin, Algebra.map_top, ← Set.range_comp] at h
  have hcoords : φ ∘ originalTensorPencilCoordinate H I E s =
      (fun i : Fin 3 => w (s.symm (some i)) / w (s.symm none)) :=
    funext (extendedClosedGaussTensorChartToOwnFunctionField_original_coordinate H I E hH e s)
  rw [hcoords] at h
  rw [projectiveCoordinateChartAlgebra_eq_three_ratios w s
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e (s.symm none))]
  exact h.symm

/-- The actual original tensor chart and native frame-ratio algebra
are isomorphic over the same extended coefficient field. -/
noncomputable def extendedClosedGaussOwnCoordinateChartEquiv :
    T₀ ≃ₐ[E] projectiveCoordinateChartAlgebra (C := E) w (s.symm none) :=
  (AlgEquiv.ofInjective (extendedClosedGaussTensorChartToOwnFunctionFieldAlgHom H I E hH e s)
    (extendedClosedGaussTensorChartToOwnFunctionField_injective H I E hH e s)).trans
      (Subalgebra.equivOfEq _ _ (extendedClosedGaussTensorChartToOwnFunctionField_range H I E hH e s))

/-- The original-to-native chart isomorphism retains every entire
original tensor value in the actual scheme function field. -/
theorem extendedClosedGaussOwnCoordinateChartEquiv_value (t : T₀) :
    (extendedClosedGaussOwnCoordinateChartEquiv H I E hH e s t : (N).functionField) =
      extendedClosedGaussTensorChartToOwnFunctionField H I E hH e s t := rfl

/-- Every actual regular normalized chart function is integral over
its native original-frame ratio algebra in the scheme's own function field. -/
theorem extendedClosedGaussNormalizedChartFunction_isIntegral_own_coordinates (r : Γ(N, Uₙ)) :
    IsIntegral (projectiveCoordinateChartAlgebra (C := E) w (s.symm none))
      ((N).germToFunctionField Uₙ r) := by
  let φ := (extendedClosedGaussNormalizedChartFunctionFieldEquiv H I E hH e s).toRingHom
  let b := (extendedClosedGaussOwnCoordinateChartEquiv H I E hH e s).toRingHom
  have hcomp : (algebraMap (projectiveCoordinateChartAlgebra (C := E) w (s.symm none))
      (N).functionField).comp b = φ.comp (algebraMap T₀ (FractionRing T₀)) := by
    apply RingHom.ext
    intro t
    exact extendedClosedGaussOwnCoordinateChartEquiv_value H I E hH e s t
  have hi := IsIntegral.map_of_comp_eq b φ hcomp
    (extendedClosedGaussNormalizedChartSectionValue_isIntegral H I E hH e s r)
  exact (extendedClosedGaussNormalizedChartFunctionFieldEquiv_section H I E hH e s r) ▸ hi

end DimensionFourDependence
