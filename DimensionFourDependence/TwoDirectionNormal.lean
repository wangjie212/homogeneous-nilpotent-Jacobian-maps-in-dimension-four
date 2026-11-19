import DimensionFourDependence.NormalSpanDependence

/-! # Two annihilated constant directions force component dependence

The coordinate-conjugacy step of Proposition 2.3 is replaced by a
coordinate-free rank-nullity argument over the original field.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Two independent constant linear relations on a four-component
family bound its component span by two. -/
theorem component_span_le_two_of_two_constant_relations
    (ν : Fin 4 → V) (v w : Fin 4 → K) (hvw : LinearIndependent K ![v, w])
    (hv : ∑ i, v i • ν i = 0) (hw : ∑ i, w i • ν i = 0) :
    finrank K (Submodule.span K (Set.range ν)) ≤ 2 := by
  let L := Fintype.linearCombination K ν
  have hle : Submodule.span K (Set.range ![v, w]) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hv
    · exact hw
  have hdim : 2 ≤ finrank K (LinearMap.ker L) := by
    have he : finrank K (Submodule.span K (Set.range ![v, w])) = 2 := by
      simpa using finrank_span_eq_card hvw
    exact he ▸ Submodule.finrank_mono hle
  have hr := LinearMap.finrank_range_add_finrank_ker L
  rw [Fintype.range_linearCombination] at hr
  simp only [Module.finrank_pi, Fintype.card_fin] at hr
  omega

variable [CharZero K]

/-- A nonzero polynomial left normal annihilating a fixed two-space
forces a constant relation among the homogeneous map components. -/
theorem dependent_of_normal_annihilates_two_directions
    (H ν : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hν : ν ≠ 0) (hker : ν ᵥ* jac H = 0)
    (v w : Fin 4 → K) (hvw : LinearIndependent K ![v, w])
    (hv : ν ⬝ᵥ (fun i => C (v i)) = 0) (hw : ν ⬝ᵥ (fun i => C (w i)) = 0) :
    ComponentsDependent H := by
  apply dependent_of_normal_component_span_le_two H ν hd hH hν hker
  apply component_span_le_two_of_two_constant_relations ν v w hvw
  · simpa only [dotProduct, MvPolynomial.smul_eq_C_mul, mul_comm] using hv
  · simpa only [dotProduct, MvPolynomial.smul_eq_C_mul, mul_comm] using hw

/-- The fixed-two-space conclusion using the actual image normal. -/
theorem ImageRelationWitness.dependent_of_annihilated_two_space
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (W : ImageRelationWitness H) (v w : Fin 4 → K) (hvw : LinearIndependent K ![v, w])
    (hv : imageRelationNormal H W.equation ⬝ᵥ (fun i => C (v i)) = 0)
    (hw : imageRelationNormal H W.equation ⬝ᵥ (fun i => C (w i)) = 0) :
    ComponentsDependent H :=
  dependent_of_normal_annihilates_two_directions H _ hd hH W.normal_ne_zero (W.left_kernel H)
    v w hvw hv hw

end DimensionFourDependence
