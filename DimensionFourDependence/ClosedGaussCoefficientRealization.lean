import DimensionFourDependence.ClosedGaussHomogeneousParameter
import DimensionFourDependence.DevelopableFirstInvariant

/-! # The actual closed Gauss parameter in the actual graph coefficient field -/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

section Closures

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- A subfield of a relative algebraic closure has its relative
algebraic closure in that same closure inside the original ambient field. -/
theorem relative_algebraic_closure_le_of_le
    (M J : IntermediateField K F)
    (hM : M ≤ (algebraicClosure J F).restrictScalars K) :
    (algebraicClosure M F).restrictScalars K ≤ (algebraicClosure J F).restrictScalars K := by
  let L := algebraicClosure J F
  let : Algebra M L := (IntermediateField.inclusion hM).toRingHom.toAlgebra
  let : IsScalarTower M L F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  intro x hx
  have hxM : IsAlgebraic M x := mem_algebraicClosure_iff.mp hx
  have hxL : IsAlgebraic L x := hxM.tower_top L
  exact mem_algebraicClosure_iff'.mpr (isIntegral_trans (R := J) (A := L) x hxL.isIntegral)

end Closures

variable {K : Type u} [Field K] [CharZero K]

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- Every transcendental element of the actual graph coefficient
field has a nonzero actual coordinate partial. -/
theorem coefficient_partials_nonzero_of_transcendental
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y)
    (t : coefficientField (K := K) Y) (ht : Transcendental K (t : S₀)) :
    ∃ j, coefficientPartial Y hY j t ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨j, hj⟩ := exists_rationalPartial_ne_zero_of_transcendental (t : S₀) ht
  apply hj
  rw [coefficient_chain_rule Y hY (rationalPartial (K := K) j) t]
  simp only [hn, IntermediateField.coe_zero, mul_zero, Finset.sum_const_zero]

variable (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))

local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))

variable (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))

local notation "L" => coefficientField (K := K) (Y)
local notation "M" => projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)

include hY hh

/-- The actual Gauss field is the actual field of graph-gradient
values, with both realized in the original rational source field. -/
theorem actual_gauss_field_eq_graph_gradient_adjoin :
    (M) = IntermediateField.adjoin K (Set.range (fiberGradient (Y) hY h)) := by
  obtain ⟨hlast, hcoord⟩ := I.gauss_chart_ratios H p hY h hh
  rw [projectiveRatioField_chart_eq (rationalImageNormal H I.equation)
    (imageNormalPivot H I) (p 3) (imageNormalPivot_ne_zero H I) hlast]
  exact projectiveRatioField_graph_chart _ p _ hlast hcoord

/-- The actual Gauss field lies in the actual graph coefficient field. -/
theorem actual_gauss_field_le_graph_coefficient_field : (M) ≤ (L).restrictScalars K := by
  rw [actual_gauss_field_eq_graph_gradient_adjoin H I p hY h hh]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  exact (coefficientPartial (Y) hY i h).property

/-- The entire relatively closed Gauss cover, including its chosen
rational parameter, lies in the actual graph coefficient field. -/
theorem actual_closed_gauss_field_le_graph_coefficient_field :
    closedGaussParameterField H I ≤ (L).restrictScalars K :=
  relative_algebraic_closure_le_of_le (M) (IntermediateField.adjoin K (Set.range (Y)))
    (actual_gauss_field_le_graph_coefficient_field H I p hY h hh)

/-- The actual graph-gradient coordinates belong to the same actual
closed Gauss field as the parameter used in the native pencil. -/
theorem actual_graph_gradient_mem_closed_gauss_field (i : Fin 3) :
    (coefficientPartial (Y) hY i h : S₀) ∈ closedGaussParameterField H I := by
  apply actual_gauss_field_le_closed_parameter_field H I
  rw [actual_gauss_field_eq_graph_gradient_adjoin H I p hY h hh]
  exact IntermediateField.subset_adjoin K _ ⟨i, rfl⟩

/-- The native pencil's chosen closed-cover parameter realized in the
actual coefficient field of this actual graph chart. -/
noncomputable def closedGaussCoefficientParameterHom
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) : RatFunc K →ₐ[K] (L) :=
  (IntermediateField.inclusion (actual_closed_gauss_field_le_graph_coefficient_field H I p hY h hh)).comp e.toAlgHom

/-- The actual graph-gradient as rational functions of that same
closed-cover parameter, without an assumed rational presentation. -/
noncomputable def closedGaussCoefficientGraphSlope
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (i : Fin 3) : RatFunc K :=
  e.symm ⟨(coefficientPartial (Y) hY i h : S₀),
    actual_graph_gradient_mem_closed_gauss_field H I p hY h hh i⟩

/-- The entire parameter realization agrees with the original source
realization used to construct the actual projective pencil. -/
theorem closedGaussCoefficientParameterHom_source_value
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (r : RatFunc K) :
    (closedGaussCoefficientParameterHom H I p hY h hh e r : S₀) =
      closedGaussParameterSourceHom H I e r := rfl

/-- The constructed rational slope recovers the actual coefficient
partial of the actual graph function at every original coordinate. -/
theorem closedGaussCoefficientGraphSlope_value
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (i : Fin 3) :
    closedGaussCoefficientParameterHom H I p hY h hh e
      (closedGaussCoefficientGraphSlope H I p hY h hh e i) = coefficientPartial (Y) hY i h := by
  apply Subtype.ext
  rw [closedGaussCoefficientParameterHom_source_value]
  unfold closedGaussCoefficientGraphSlope
  change (e (e.symm _) : S₀) = (coefficientPartial (Y) hY i h : S₀)
  rw [e.apply_symm_apply]

/-- A nonzero actual coefficient partial of the closed Gauss parameter
is constructed from its original-source transcendence. -/
theorem closedGaussCoefficientParameterHom_partial_ne_zero
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) :
    ∃ j, coefficientPartial (Y) hY j
      (closedGaussCoefficientParameterHom H I p hY h hh e RatFunc.X) ≠ 0 := by
  apply coefficient_partials_nonzero_of_transcendental (Y) hY
  simpa only [closedGaussCoefficientParameterHom_source_value] using
    closedGaussParameterSourceHom_X_transcendental H I e

end DimensionFourDependence
