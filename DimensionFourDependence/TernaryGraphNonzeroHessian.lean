import DimensionFourDependence.TernaryGraphPlaneDifferentiation
import DimensionFourDependence.ClosedFieldCoefficientPartials

/-! # A zero output Hessian would give an original affine relation -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

set_option maxHeartbeats 1650000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)

theorem closed_field_ternary_graph_zero_hessian_gives_affine_relation
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w : coefficientField (K := K) Y)
    (hz : ternaryGraphHessian Y hY w = 0) :
    ∃ (c : Fin 2 → K) (b : K), (w : F) = (∑ i, algebraMap K F (c i) * Y i) + algebraMap K F b := by
  let L := coefficientField (K := K) Y
  let : IsScalarTower K L F := coefficientFieldScalarTower Y
  let E := IntermediateField.adjoin K (Set.range Y)
  let y : Fin 2 → L := fun i => algebraMap E L (outputCoordinate (K := K) Y i)
  have hconst (j : Fin 2) :
      ∃ c : K, algebraMap K L c = coefficientPartial Y hY j w := by
    apply closed_field_coefficientPartials_common_constant_is_scalar Y hY
    intro i
    apply Subtype.ext
    exact congrFun (congrFun hz i) j
  choose c hc using hconst
  let a : L := w - ∑ i : Fin 2, algebraMap K L (c i) * y i
  have ha (j : Fin 2) : coefficientPartial Y hY j a = 0 := by
    have hy (i : Fin 2) : coefficientPartial Y hY j (y i) = if i = j then 1 else 0 :=
      coefficientPartial_coordinate Y hY j i
    have hscalar (i : Fin 2) : coefficientPartial Y hY j (algebraMap K L (c i)) = 0 :=
      (coefficientPartial Y hY j).map_algebraMap (c i)
    have h : coefficientPartial Y hY j (∑ i : Fin 2, algebraMap K L (c i) * y i) = algebraMap K L (c j) := by
      rw [map_sum]
      simp only [Derivation.leibniz, hscalar, hy, smul_eq_mul]
      simp
    change coefficientPartial Y hY j (w - ∑ i : Fin 2, algebraMap K L (c i) * y i) = 0
    rw [map_sub, h, hc j, sub_self]
  obtain ⟨b, hb⟩ := closed_field_coefficientPartials_common_constant_is_scalar Y hY a ha
  refine ⟨c, b, ?_⟩
  have hy (i : Fin 2) : algebraMap L F (y i) = Y i := rfl
  have he : algebraMap K F b = (w : F) - ∑ i, algebraMap K F (c i) * Y i := by
    have h := congrArg (algebraMap L F) hb
    change algebraMap L F (algebraMap K L b) =
      algebraMap L F (w - ∑ i : Fin 2, algebraMap K L (c i) * y i) at h
    simpa only [map_sub, map_sum, map_mul, hy, ← IsScalarTower.algebraMap_apply K L F,
      IntermediateField.algebraMap_apply] using h
  linear_combination -he

/-- The leading quadratic coefficient of the embedded generic curve
is nonzero for linearly independent components normalized at the origin. -/
theorem closed_field_normalized_ternary_graph_hessian_ne_zero
    (H : Fin 3 → R₃) (h0 : ∀ j, aeval (fun _ : Fin 3 => (0 : K)) (H j) = 0)
    (hind : ¬ComponentsDependent H)
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (hpair : ∀ i : Fin 2, Y i = ι (H i.castSucc))
    (w : coefficientField (K := K) Y) (hw : (w : F) = ι (H 2)) :
    ternaryGraphHessian Y hY w ≠ 0 := by
  intro hz
  obtain ⟨c, b, ha⟩ := closed_field_ternary_graph_zero_hessian_gives_affine_relation Y hY w hz
  have hpoly : H 2 = (C (c 0) * H 0 + C (c 1) * H 1) + C b := by
    apply IsFractionRing.injective R₃ F
    rw [hw, Fin.sum_univ_two, hpair, hpair] at ha
    have he (a : K) : ι (C a) = algebraMap K F a := by
      rw [← algebraMap_eq, ← IsScalarTower.algebraMap_apply K R₃ F]
    rw [map_add, map_add, map_mul, map_mul, he, he, he]
    exact ha
  have hb : b = 0 := by
    have h := congrArg (aeval (fun _ : Fin 3 => (0 : K))) hpoly
    have he (a : K) : aeval (fun _ : Fin 3 => (0 : K)) (C a : R₃) = a := by simp
    simpa only [map_add, map_mul, h0, he, mul_zero, add_zero, zero_add] using h.symm
  have hr : H 2 = C (c 0) * H 0 + C (c 1) * H 1 := by
    simpa only [hb, map_zero, add_zero] using hpoly
  apply hind
  refine ⟨![-c 0, -c 1, 1], ?_, ?_⟩
  · intro h
    have he := congrFun h (2 : Fin 3)
    simp at he
  · rw [Fin.sum_univ_three]
    change (-c 0) • H 0 + (-c 1) • H 1 + (1 : K) • H 2 = 0
    rw [one_smul, smul_eq_C_mul, smul_eq_C_mul, map_neg, map_neg]
    linear_combination hr

end DimensionFourDependence
