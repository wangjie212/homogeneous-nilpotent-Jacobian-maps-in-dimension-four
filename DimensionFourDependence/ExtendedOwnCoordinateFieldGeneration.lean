import DimensionFourDependence.ExtendedOwnFunctionFieldEquiv
import DimensionFourDependence.ExtendedOriginalHomogeneousRelations
import DimensionFourDependence.NormalizationResidueDimensionExact
import DimensionFourDependence.GeneratedFieldDimension

/-! # The original native affine coordinates generate the whole actual surface field -/

namespace DimensionFourDependence

/-- An actual fraction-field identification retains generation by
the original algebra coordinates, without a new field-generation assumption. -/
theorem fraction_equiv_field_adjoin_original_coordinates
    {k A F σ : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Field F] [Algebra k F]
    (b : FractionRing A ≃ₐ[k] F) (g : A →ₐ[k] F)
    (hcomp : b.toAlgHom.toRingHom.comp (algebraMap A (FractionRing A)) = g.toRingHom)
    (x : σ → A) (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    IntermediateField.adjoin k (Set.range (fun i => g (x i))) = ⊤ := by
  have hr := congrArg (Subalgebra.map g) hx
  rw [AlgHom.map_adjoin, Algebra.map_top, ← Set.range_comp] at hr
  have hfield := IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq
    (f := b.toAlgHom) (g := g) hcomp hr.symm
  exact hfield.symm.trans b.fieldRange_eq_top

universe u

/-- When the original coordinates generate a whole field, the
coordinate algebra has that same transcendence degree. -/
theorem original_coordinate_algebra_trdeg_eq_full_field
    {k F : Type u} [Field k] [Field F] [Algebra k F] (x : Fin 3 → F)
    (hx : IntermediateField.adjoin k (Set.range x) = ⊤) :
    Algebra.trdeg k (Algebra.adjoin k (Set.range x)) = Algebra.trdeg k F :=
  (generatedField_trdeg_eq_generatedAlgebra (Set.range x)).symm.trans
    (((IntermediateField.equivOfEq hx).trans IntermediateField.topEquiv).trdeg_eq)

open AlgebraicGeometry
open scoped TensorProduct

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
local notation "T₀" s:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm s none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "s₀" => finSuccEquiv' (0 : Fin 4)

local instance extendedOwnCoordinateFieldGenerationIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance extendedOwnCoordinateFieldGenerationDomain (s : Fin 4 ≃ Option (Fin 3)) : IsDomain (T₀ s) :=
  original_tensor_pencil_chart_isDomain H I E s
noncomputable local instance extendedOwnCoordinateFieldGenerationAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- In each original chart, the three original native coordinate
ratios generate the whole actual scheme function field. -/
theorem extendedClosedGaussNormalization_original_ratio_field_top
    (s : Fin 4 ≃ Option (Fin 3)) :
    IntermediateField.adjoin E (Set.range (fun i : Fin 3 =>
      w (s.symm (some i)) / w (s.symm none))) = ⊤ := by
  let b := extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e s
  let g := extendedClosedGaussTensorChartToOwnFunctionFieldAlgHom H I E hH e s
  have hcomp : b.toAlgHom.toRingHom.comp (algebraMap (T₀ s) (FractionRing (T₀ s))) = g.toRingHom := by
    apply RingHom.ext
    intro t
    rfl
  have h := fraction_equiv_field_adjoin_original_coordinates b g hcomp
    (originalTensorPencilCoordinate H I E s) (originalTensorPencilCoordinate_adjoin H I E s)
  have hcoords : (fun i => g (originalTensorPencilCoordinate H I E s i)) =
      (fun i => w (s.symm (some i)) / w (s.symm none)) :=
    funext (extendedClosedGaussTensorChartToOwnFunctionField_original_coordinate H I E hH e s)
  exact (congrArg (fun x : Fin 3 → (N).functionField => IntermediateField.adjoin E (Set.range x))
    hcoords).symm.trans h

/-- The actual normalization function field has the original
pencil's relative surface dimension two. -/
theorem extendedClosedGaussNormalization_functionField_trdeg_two
    (hGauss : gaussImageDimension H I = 1) : Algebra.trdeg E (N).functionField = 2 := by
  let : IsDomain (T₀ s₀) := original_tensor_pencil_chart_isDomain H I E s₀
  exact (extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e s₀).trdeg_eq.symm.trans
    ((fractionRing_trdeg_eq_base (k := E) (A := T₀ s₀)).trans
      (original_tensor_pencil_trdeg_two H I E hH e hGauss s₀))

/-- With the actual original zeroth frame, its weight is one and
the remaining three actual weights generate the whole native field. -/
theorem extendedClosedGaussNormalization_original_affine_field_top :
    IntermediateField.adjoin E (Set.range (fun i : Fin 3 => w ((s₀).symm (some i)))) = ⊤ := by
  have h := extendedClosedGaussNormalization_original_ratio_field_top H I E hH e s₀
  have hcoords : (fun i : Fin 3 => w ((s₀).symm (some i)) / w ((s₀).symm none)) =
      (fun i : Fin 3 => w ((s₀).symm (some i))) := by
    funext i
    rw [finSuccEquiv'_symm_none, extendedClosedGaussNormalizationHyperplaneWeight_zero, div_one]
  exact (congrArg (fun x : Fin 3 → (N).functionField => IntermediateField.adjoin E (Set.range x))
    hcoords).symm.trans h

/-- The three actual affine native weights generate an actual
two-dimensional coefficient algebra, not merely an unspecified subfield. -/
theorem extendedClosedGaussNormalization_original_affine_algebra_trdeg_two
    (hGauss : gaussImageDimension H I = 1) :
    Algebra.trdeg E (Algebra.adjoin E (Set.range (fun i : Fin 3 => w ((s₀).symm (some i))))) = 2 :=
  (original_coordinate_algebra_trdeg_eq_full_field _
    (extendedClosedGaussNormalization_original_affine_field_top H I E hH e)).trans
      (extendedClosedGaussNormalization_functionField_trdeg_two H I E hH e hGauss)

end DimensionFourDependence
