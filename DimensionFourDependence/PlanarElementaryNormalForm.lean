import DimensionFourDependence.PlanarActiveNormalization
import DimensionFourDependence.ReducedPencilVertexDifferential
import DimensionFourDependence.Nilpotent
import DimensionFourDependence.Tame

/-! # The elementary case of Proposition 6.3 -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K

/-- If either normalized component vanishes, trace zero forces the other
component to be independent of its own coordinate. -/
theorem normalized_planar_zero_component_is_elementary
    (A : Fin 2 → R₄) (hN : IsNilpotent (planarActiveJacobian A))
    (h : planarActiveNormalized (A 0) = 0 ∨ planarActiveNormalized (A 1) = 0) :
    ∃ (i : Fin 4) (p : R₄) (hp : i ∉ p.vars), ∀ j,
      Tame.elementary i p hp (X j) =
        X j + ![planarActiveNormalized (A 0), planarActiveNormalized (A 1), 0, 0] j := by
  let B : Fin 2 → R₄ := fun i => planarActiveNormalized (A i)
  have hN' : IsNilpotent (planarActiveJacobian B) := by
    rw [planarActiveJacobian_normalized]
    exact hN
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hN').eq_zero
  change B 0 = 0 ∨ B 1 = 0 at h
  change ∑ i : Fin 2, pderiv (i.castAdd 2) (B i) = 0 at ht
  rw [Fin.sum_univ_two] at ht
  change pderiv 0 (B 0) + pderiv 1 (B 1) = 0 at ht
  rcases h with hz | hz
  · have hd : pderiv 1 (B 1) = 0 := by simpa only [hz, map_zero, zero_add] using ht
    have hv : (1 : Fin 4) ∉ (B 1).vars := fun hv =>
      (mem_vars_iff_degreeOf_ne_zero.mp hv) (degreeOf_eq_zero_of_pderiv_eq_zero _ _ hd)
    refine ⟨1, B 1, hv, ?_⟩
    intro j
    rw [Tame.elementary_X]
    change X j + (if j = 1 then B 1 else 0) = X j + ![B 0, B 1, 0, 0] j
    fin_cases j <;> simp [hz]
  · have hd : pderiv 0 (B 0) = 0 := by simpa only [hz, map_zero, add_zero] using ht
    have hv : (0 : Fin 4) ∉ (B 0).vars := fun hv =>
      (mem_vars_iff_degreeOf_ne_zero.mp hv) (degreeOf_eq_zero_of_pderiv_eq_zero _ _ hd)
    refine ⟨0, B 0, hv, ?_⟩
    intro j
    rw [Tame.elementary_X]
    change X j + (if j = 0 then B 0 else 0) = X j + ![B 0, B 1, 0, 0] j
    fin_cases j <;> simp [hz]

end DimensionFourDependence.Shear
