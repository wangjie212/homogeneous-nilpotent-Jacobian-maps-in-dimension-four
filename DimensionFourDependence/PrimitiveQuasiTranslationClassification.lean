import DimensionFourDependence.PrimitiveGordanNoetherSpan
import DimensionFourDependence.QuasiTranslationSpanReduction

/-! # The complete primitive positive quasi-translation branch of Proposition 2.1 -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- The primitive positive homogeneous four-variable quasi-translation
constructs its actual binary two-axis normal form. The inverse matrices,
both surviving coprime homogeneous forms, all four vertical partial
identities and both nonzero entries are constructed from the original
direction alone. No classification result is supplied. -/
theorem primitive_positive_homogeneous_quasi_translation_constructs_binary_two_axis_conjugacy
    (u : Fin 4 → R₀) {e : ℕ} (he : 0 < e) (hUne : u ≠ 0)
    (hhom : IsHomogMap u e) (hprim : IsPrimitiveVec u) (hacc : jac u *ᵥ u = 0) :
    ∃ (T S : Matrix (Fin 4) (Fin 4) K) (A B : R₀),
      T * S = 1 ∧ S * T = 1 ∧ linearPolynomialConjugate T S u = ![0, 0, A, B] ∧
      A.IsHomogeneous e ∧ B.IsHomogeneous e ∧ IsRelPrime A B ∧ A ≠ 0 ∧ B ≠ 0 ∧
      pderiv 2 A = 0 ∧ pderiv 3 A = 0 ∧ pderiv 2 B = 0 ∧ pderiv 3 B = 0 := by
  obtain ⟨r, s, hli, hr, hs⟩ :=
    primitive_positive_homogeneous_quasi_translation_constructs_two_constant_relations u he hUne hhom hprim hacc
  obtain ⟨T, S, A, B, hTS, hST, hform⟩ :=
    two_independent_constant_relations_construct_two_axis_conjugacy u r s hli hr hs
  have hhom' := linearPolynomialConjugate_homogeneous T S u hhom
  have hprim' := linearPolynomialConjugate_preserves_primitive_vector T S hTS hST u hprim
  have hacc' := linearPolynomialConjugate_preserves_polynomial_right_kernel T S hTS u u hacc
  rw [hform] at hhom' hprim' hacc'
  obtain ⟨hAz, hAw, hBz, hBw⟩ :=
    primitive_two_axis_homogeneous_zero_acceleration_has_binary_entries A B (hhom' 2) (hhom' 3) hprim' hacc'
  obtain ⟨hA0, hB0, _hWr⟩ := primitive_positive_binary_direction_entries_and_wronskian_nonzero
    A B he (hhom' 2) (hhom' 3) hprim' hAz hAw hBz hBw
  exact ⟨T, S, A, B, hTS, hST, hform, hhom' 2, hhom' 3,
    primitive_two_axis_entries_isRelPrime A B hprim', hA0, hB0, hAz, hAw, hBz, hBw⟩

/-- The entire positive-degree primitive zero-acceleration kernel
branch of Proposition 2.1. Classification coordinates, component span,
binary forms and all trace constraints are constructed internally. -/
theorem primitive_positive_zero_acceleration_kernel_forces_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (u : Fin 4 → R₀) {e : ℕ}
    (hu : IsPrimRightKernel (jac H) u e) (he : 0 < e) (hacc : jac u *ᵥ u = 0) :
    ComponentsDependent H :=
  primitive_positive_zero_acceleration_kernel_small_component_span_forces_componentsDependent
    H hd hH hN u hu he hacc
    (primitive_positive_homogeneous_quasi_translation_component_span_at_most_two
      u he hu.ne_zero hu.homog hu.prim hacc)

/-- Every remaining independent original rank-three map constructs a
degree-zero primitive kernel. The nonlinear-fiber branch, actual line
fibers, quasi-translation construction and the entire positive-degree
classification obstruction have all been discharged. -/
theorem original_independent_rank_three_map_constructs_degree_zero_primitive_kernel
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) :
    ∃ u : Fin 4 → R₀, IsPrimRightKernel (jac H) u 0 := by
  obtain ⟨u, e, hu, hacc⟩ :=
    original_independent_rank_three_map_constructs_zero_acceleration_kernel H hd hH hN hrank hind
  have he : e = 0 := by
    by_contra hn
    exact hind (primitive_positive_zero_acceleration_kernel_forces_componentsDependent
      H hd hH hN u hu (Nat.pos_of_ne_zero hn) hacc)
  exact ⟨u, he ▸ hu⟩

/-- The remaining original rank-three counterexample has an actual
nonzero original constant right-kernel vector. No constant direction,
geometric fiber or normal-form data are supplied. -/
theorem original_independent_rank_three_map_constructs_nonzero_constant_right_kernel
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) :
    ∃ c : Fin 4 → K, c ≠ 0 ∧ jac H *ᵥ (fun i => C (c i)) = 0 := by
  obtain ⟨u, hu⟩ := original_independent_rank_three_map_constructs_degree_zero_primitive_kernel
    H hd hH hN hrank hind
  let c : Fin 4 → K := fun i => (u i).coeff 0
  have huc : u = fun i => C (c i) := funext (fun i => eq_C_of_isHomogeneous_zero (hu.homog i))
  have hc : c ≠ 0 := by
    intro hz
    apply hu.ne_zero
    rw [huc]
    funext i
    rw [show c i = 0 from congrFun hz i, map_zero]
    rfl
  exact ⟨c, hc, by rw [← huc]; exact hu.ker⟩

/-- Native rank-three reduction of Theorem 1.1 over closed original
constants: component dependence holds, or the original map has a nonzero
constant kernel direction. Only the homogeneous three-variable step
remains in this rank-three branch. -/
theorem original_homogeneous_nilpotent_rank_three_dependent_or_constant_right_kernel
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) :
    ComponentsDependent H ∨ ∃ c : Fin 4 → K, c ≠ 0 ∧ jac H *ᵥ (fun i => C (c i)) = 0 := by
  by_cases hind : ComponentsDependent H
  · exact Or.inl hind
  · exact Or.inr (original_independent_rank_three_map_constructs_nonzero_constant_right_kernel H hd hH hN hrank hind)

end DimensionFourDependence
