import DimensionFourDependence.TernaryFixedCoordinateTriangularForm
import DimensionFourDependence.LinearConjugacyComposition
import DimensionFourDependence.OriginalFieldTernaryDependence
import DimensionFourDependence.ReducedPencilVertexDifferential

/-! # The leading homogeneous ternary triangular frame over the original field -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 1900000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₃" => MvPolynomial (Fin 3) K

/-- The leading homogeneous perturbation admits a triangular constant
frame with one binary form and one pure power. -/
theorem homogeneous_ternary_nilpotent_constructs_triangular_frame
    (H : Fin 3 → R₃) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H)) :
    ∃ (T S : Matrix (Fin 3) (Fin 3) K) (P : R₂) (c : K),
      T * S = 1 ∧ S * T = 1 ∧ P.IsHomogeneous d ∧
      linearPolynomialConjugate T S H = ![rename Fin.succ P, C c * X 2 ^ d, 0] := by
  have hd₀ := original_field_positive_homogeneous_ternary_nilpotent_componentsDependent H hd hH hN
  obtain ⟨A, B, hAB, hBA, hz⟩ :=
    constant_relation_constructs_zero_component_conjugacy H hd₀ (Fin.last 2)
  let G := linearPolynomialConjugate A B H
  have hG := linearPolynomialConjugate_homogeneous A B H hH
  have hGn := linearPolynomialConjugate_nilpotent A B hAB hBA H hN
  obtain ⟨U, V, Q, c, hUV, hVU, hQ, hx⟩ :=
    homogeneous_ternary_fixed_last_constructs_triangular_form G hG hGn hz
  have hQh : Q.IsHomogeneous d := by
    have h := linearPolynomialConjugate_homogeneous U V G hG 0
    rw [hQ] at h
    exact h
  have hv : (0 : Fin 3) ∉ Q.vars := by
    intro hm
    exact (mem_vars_iff_degreeOf_ne_zero.mp hm) (degreeOf_eq_zero_of_pderiv_eq_zero _ _ hx)
  have hsubset : (↑Q.vars : Set (Fin 3)) ⊆ Set.range (Fin.succ : Fin 2 → Fin 3) := by
    intro i hi
    refine Fin.cases ?_ (fun j hj => ⟨j, rfl⟩) i hi
    intro he
    exact (hv he).elim
  obtain ⟨P, hP⟩ := exists_rename_eq_of_vars_subset_range Q
    (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2) hsubset
  have hPh : P.IsHomogeneous d :=
    (IsHomogeneous.rename_isHomogeneous_iff (Fin.succ_injective 2)).mp (hP.symm ▸ hQh)
  have h₁ : (A * U) * (V * B) = 1 := by
    calc
      _ = A * (U * V) * B := by simp only [mul_assoc]
      _ = _ := by rw [hUV, mul_one, hAB]
  have h₂ : (V * B) * (A * U) = 1 := by
    calc
      _ = V * (B * A) * U := by simp only [mul_assoc]
      _ = _ := by rw [hBA, mul_one, hVU]
  refine ⟨A * U, V * B, P, c, h₁, h₂, hPh, ?_⟩
  rw [← linearPolynomialConjugate_compose A B U V H]
  change linearPolynomialConjugate U V G = _
  rw [hQ, hP]

end DimensionFourDependence
