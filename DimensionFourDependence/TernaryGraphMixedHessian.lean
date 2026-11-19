import DimensionFourDependence.TernaryGraphNonzeroHessian
import DimensionFourDependence.CoefficientEuler

/-! # The zero diagonal Hessian integrates to an actual mixed product -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2100000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "F" => FractionRing (MvPolynomial (Fin 3) K)

/-- With zero diagonal Hessian, the mixed derivative is a nonzero
original scalar, and the last output is the corresponding bilinear
polynomial plus an original affine linear form in the two outputs. -/
theorem ternary_graph_zero_hessian_diagonal_constructs_bilinear_output
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w : coefficientField (K := K) Y)
    (h₀ : coefficientPartial Y hY 0 (coefficientPartial Y hY 0 w) = 0)
    (h₁ : coefficientPartial Y hY 1 (coefficientPartial Y hY 1 w) = 0)
    (hne : ternaryGraphHessian Y hY w ≠ 0) :
    ∃ γ α β δ : K, γ ≠ 0 ∧ (w : F) =
      algebraMap K F γ * Y 0 * Y 1 + algebraMap K F α * Y 0 +
        algebraMap K F β * Y 1 + algebraMap K F δ := by
  let L := coefficientField (K := K) Y
  let : IsScalarTower K L F := coefficientFieldScalarTower Y
  let D := coefficientPartial Y hY 0
  let E := coefficientPartial Y hY 1
  let m := D (E w)
  have hcomm (v : L) : D (E v) = E (D v) := coefficientPartials_commute Y hY 0 1 v
  have hm₀ : D m = 0 := calc
    _ = D (E (D w)) := congrArg D (hcomm w)
    _ = E (D (D w)) := hcomm (D w)
    _ = _ := by change E (D (D w)) = 0; rw [show D (D w) = 0 from h₀, map_zero]
  have hm₁ : E m = 0 := calc
    _ = D (E (E w)) := (hcomm (E w)).symm
    _ = _ := by change D (E (E w)) = 0; rw [show E (E w) = 0 from h₁, map_zero]
  obtain ⟨γ, hγ⟩ := closed_field_coefficientPartials_common_constant_is_scalar Y hY m (by
    intro i
    fin_cases i
    · exact hm₀
    · exact hm₁)
  have hγ0 : γ ≠ 0 := by
    intro hg
    have hm : m = 0 := by rw [hg, map_zero] at hγ; exact hγ.symm
    have hm' : E (D w) = 0 := (hcomm w).symm.trans hm
    apply hne
    funext i j
    have ht (i j : Fin 2) : coefficientPartial Y hY i (coefficientPartial Y hY j w) = 0 := by
      fin_cases i <;> fin_cases j
      · exact h₀
      · exact hm
      · exact hm'
      · exact h₁
    change (algebraMap L F) (coefficientPartial Y hY i (coefficientPartial Y hY j w)) = 0
    rw [ht, map_zero]
  let u := coefficientCoordinate (K := K) Y 0
  let v := coefficientCoordinate (K := K) Y 1
  let c := algebraMap K L γ
  let a : L := w - c * (u * v)
  have hCoord (i j : Fin 2) : coefficientPartial Y hY i (coefficientCoordinate (K := K) Y j) =
      if j = i then 1 else 0 := coefficientPartial_coordinate Y hY i j
  have hDu : D u = 1 := (hCoord 0 0).trans (by simp)
  have hDv : D v = 0 := (hCoord 0 1).trans (by simp [show (1 : Fin 2) ≠ 0 by decide])
  have hEu : E u = 0 := (hCoord 1 0).trans (by simp [show (0 : Fin 2) ≠ 1 by decide])
  have hEv : E v = 1 := (hCoord 1 1).trans (by simp)
  have hDa : D a = D w - c * v := by
    change D (w - c * (u * v)) = D w - c * v
    have hc : D c = 0 := D.map_algebraMap γ
    simp only [map_sub, Derivation.leibniz, hc, hDu, hDv, smul_eq_mul, mul_zero,
      add_zero, zero_add, mul_one]
  have hEa : E a = E w - c * u := by
    change E (w - c * (u * v)) = E w - c * u
    have hc : E c = 0 := E.map_algebraMap γ
    simp only [map_sub, Derivation.leibniz, hc, hEu, hEv, smul_eq_mul, mul_zero,
      add_zero, zero_add, mul_one]
  have hH : ternaryGraphHessian Y hY a = 0 := by
    have hDc : D c = 0 := D.map_algebraMap γ
    have hEc : E c = 0 := E.map_algebraMap γ
    have h₀' : D (D w) = 0 := h₀
    have h₁' : E (E w) = 0 := h₁
    have hmix : D (E w) = c := hγ.symm
    have hmix' : E (D w) = c := (hcomm w).symm.trans hmix
    have hpart (i j : Fin 2) : coefficientPartial Y hY i (coefficientPartial Y hY j a) = 0 := by
      fin_cases i <;> fin_cases j
      · change D (D a) = 0
        simp only [hDa, map_sub, Derivation.leibniz, h₀', hDc, hDv, smul_eq_mul,
          mul_zero, add_zero, sub_zero]
      · change D (E a) = 0
        simp only [hEa, map_sub, Derivation.leibniz, hmix, hDc, hDu, smul_eq_mul,
          mul_one, mul_zero, add_zero, sub_self]
      · change E (D a) = 0
        simp only [hDa, map_sub, Derivation.leibniz, hmix', hEc, hEv, smul_eq_mul,
          mul_one, mul_zero, add_zero, sub_self]
      · change E (E a) = 0
        simp only [hEa, map_sub, Derivation.leibniz, h₁', hEc, hEu, smul_eq_mul,
          mul_zero, add_zero, sub_zero]
    funext i j
    change (algebraMap L F) (coefficientPartial Y hY i (coefficientPartial Y hY j a)) = 0
    rw [hpart, map_zero]
  obtain ⟨b, δ, ha⟩ := closed_field_ternary_graph_zero_hessian_gives_affine_relation Y hY a hH
  refine ⟨γ, b 0, b 1, δ, hγ0, ?_⟩
  change algebraMap L F (w - algebraMap K L γ * (u * v)) = _ at ha
  simp only [map_sub, map_mul, ← IsScalarTower.algebraMap_apply K L F, IntermediateField.algebraMap_apply,
    u, v, coefficientCoordinate_coe, Fin.sum_univ_two] at ha
  linear_combination ha

end DimensionFourDependence
