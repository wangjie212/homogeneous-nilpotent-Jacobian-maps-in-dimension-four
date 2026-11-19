import DimensionFourDependence.ClosedGaussCoefficientRealization
import DimensionFourDependence.RelativelyClosedAlgebraicBaseChange

/-! # Coefficient-field tensors over the actual closed Gauss field are fields

The actual relatively closed Gauss field embeds in the graph coefficient
field through their original source realizations. Relative closedness
descends from the full source to this intermediate field. Every algebraic
extension of the Gauss coefficients therefore gives an actual tensor field,
so its realization in a boundary field is faithful.
-/

namespace DimensionFourDependence

open scoped TensorProduct

section Fields

variable {C L F : Type*} [Field C] [Field L] [Field F]
    [Algebra C L] [Algebra C F] [Algebra L F] [IsScalarTower C L F]

/-- Relative algebraic closedness descends to every compatible
intermediate field of the original ambient field. -/
theorem relatively_closed_in_intermediate_field
    (hclosed : algebraicClosure C F = ⊥) : algebraicClosure C L = ⊥ := by
  apply bot_unique
  intro x hx
  have hxf : IsAlgebraic C (algebraMap L F x) :=
    (mem_algebraicClosure_iff.mp hx).algHom (IsScalarTower.toAlgHom C L F)
  have hm : algebraMap L F x ∈ algebraicClosure C F := mem_algebraicClosure_iff.mpr hxf
  rw [hclosed, IntermediateField.mem_bot] at hm
  obtain ⟨c, hc⟩ := hm
  apply IntermediateField.mem_bot.mpr
  refine ⟨c, ?_⟩
  apply (algebraMap L F).injective
  rw [← IsScalarTower.algebraMap_apply C L F]
  exact hc

end Fields

section Inclusions

variable {K B F : Type*} [Field K] [Field B] [Field F]
    [Algebra K B] [Algebra K F] [Algebra B F] [IsScalarTower K B F]

/-- A source-realized intermediate-field inclusion preserves its ambient
scalar action, independently of the proof constructing that inclusion. -/
theorem intermediateFieldInclusion_source_tower
    (M : IntermediateField K F) (J : IntermediateField B F)
    (hM : M ≤ J.restrictScalars K) :
    letI : Algebra M J := (IntermediateField.inclusion hM).toRingHom.toAlgebra
    IsScalarTower M J F := by
  let : Algebra M J := (IntermediateField.inclusion hM).toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

end Inclusions

attribute [local instance] coefficientFieldScalarTower

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "C₀" => closedGaussParameterField H I

/-- The original-source inclusion of the actual closed Gauss field
in the actual graph coefficient field. -/
noncomputable def actualClosedGaussCoefficientHom : C₀ →ₐ[K] (L) :=
  IntermediateField.inclusion (actual_closed_gauss_field_le_graph_coefficient_field H I p hY h hh)

/-- The actual closed Gauss action on the coefficient field retains
its original source realization. -/
@[instance_reducible]
noncomputable def actualClosedGaussCoefficientAlgebra : Algebra C₀ (L) :=
  (actualClosedGaussCoefficientHom H I p hY h hh).toRingHom.toAlgebra

/-- The actual closed Gauss action agrees with the original-source
inclusion through the entire coefficient field. -/
theorem actualClosedGaussCoefficientAlgebra_source_tower :
    letI : Algebra C₀ (L) := actualClosedGaussCoefficientAlgebra H I p hY h hh
    IsScalarTower C₀ (L) S₀ := by
  let : Algebra C₀ (L) := actualClosedGaussCoefficientAlgebra H I p hY h hh
  exact intermediateFieldInclusion_source_tower (C₀) (L)
    (actual_closed_gauss_field_le_graph_coefficient_field H I p hY h hh)

/-- The same actual closed Gauss action also preserves every
original constant in the coefficient field. -/
theorem actualClosedGaussCoefficientAlgebra_constant_tower :
    letI : Algebra C₀ (L) := actualClosedGaussCoefficientAlgebra H I p hY h hh
    IsScalarTower K C₀ (L) := by
  let : Algebra C₀ (L) := actualClosedGaussCoefficientAlgebra H I p hY h hh
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The original closed Gauss field is relatively algebraically
closed inside the actual graph coefficient field itself. -/
theorem actual_closed_gauss_relatively_closed_in_coefficient_field :
    letI : Algebra C₀ (L) := actualClosedGaussCoefficientAlgebra H I p hY h hh
    algebraicClosure C₀ (L) = ⊥ := by
  let : Algebra C₀ (L) := actualClosedGaussCoefficientAlgebra H I p hY h hh
  let : IsScalarTower C₀ (L) S₀ := actualClosedGaussCoefficientAlgebra_source_tower H I p hY h hh
  exact relatively_closed_in_intermediate_field (F := S₀) (closedGaussParameterField_relatively_closed H I)

/-- Every actual algebraic extension of the closed Gauss coefficients
gives a tensor field for the actual graph coefficient field. -/
theorem actual_closed_gauss_coefficient_tensor_isField
    (E : Type u) [Field E] [Algebra C₀ E] [Algebra.IsAlgebraic C₀ E] :
    letI : Algebra C₀ (L) := actualClosedGaussCoefficientAlgebra H I p hY h hh
    IsField ((L) ⊗[C₀] E) := by
  let : Algebra C₀ (L) := actualClosedGaussCoefficientAlgebra H I p hY h hh
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  exact algebraic_tensor_isField_of_relatively_closed
    (actual_closed_gauss_relatively_closed_in_coefficient_field H I p hY h hh)

end DimensionFourDependence
