import DimensionFourDependence.GaussFiberDimension
import DimensionFourDependence.ClosedGaussParameterField

/-! # Algebraic constant extensions retain algebraicity in a compatible source realization -/

namespace DimensionFourDependence

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- If every original coefficient image is algebraic over the target
field, then the same holds for every compatibly realized algebraic
coefficient extension. Both coefficient maps are the given actual maps. -/
theorem compatible_algebraic_constant_extension_images_algebraic
    {D A B G : Type*} [Field D] [Field A] [Field B] [Field G]
    [Algebra D G] [Algebra A B] [Algebra.IsAlgebraic A B]
    (a : A →+* G) (b : B →+* G)
    (hcompat : ∀ x : A, b (algebraMap A B x) = a x)
    (ha : ∀ x : A, IsAlgebraic D (a x)) (y : B) : IsAlgebraic D (b y) := by
  let J := algebraicClosure D G
  let aJ : A →+* J :=
    { toFun := fun x => ⟨a x, mem_algebraicClosure_iff.mpr (ha x)⟩
      map_zero' := Subtype.ext (map_zero a)
      map_one' := Subtype.ext (map_one a)
      map_add' := fun x y => Subtype.ext (map_add a x y)
      map_mul' := fun x y => Subtype.ext (map_mul a x y) }
  letI : Algebra A J := aJ.toAlgebra
  letI : Algebra A G := a.toAlgebra
  letI : IsScalarTower A J G := IsScalarTower.of_algebraMap_eq' rfl
  let bA : B →ₐ[A] G := { b with commutes' := hcompat }
  have hA : IsAlgebraic A (b y) := (Algebra.IsAlgebraic.isAlgebraic y).algHom bA
  have hJ : IsAlgebraic J (b y) := hA.tower_top J
  exact (isIntegral_trans (R := D) (A := J) (b y) hJ.isIntegral).isAlgebraic

/-- Every element of the original closed Gauss field is algebraic
over the entire original output field K(H), using the actual Gauss
field inclusion in that output field. -/
theorem original_closed_gauss_coefficient_algebraic_over_full_output
    {K : Type*} [Field K] (H : Fin 4 → MvPolynomial (Fin 4) K)
    (I : ImageRelationWitness H) (c : closedGaussParameterField H I) :
    IsAlgebraic (polynomialOutputField H)
      (c : FractionRing (MvPolynomial (Fin 4) K)) := by
  let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
  let D := polynomialOutputField H
  let S := FractionRing (MvPolynomial (Fin 4) K)
  letI : Algebra M D := (IntermediateField.inclusion (actual_gauss_field_le_output_field H I)).toRingHom.toAlgebra
  letI : IsScalarTower M D S := IsScalarTower.of_algebraMap_eq' rfl
  have hc : IsAlgebraic M (c : S) := mem_algebraicClosure_iff.mp c.property
  exact hc.tower_top D

end DimensionFourDependence
