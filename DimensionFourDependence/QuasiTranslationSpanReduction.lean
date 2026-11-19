import DimensionFourDependence.IndependentCovectorPairCoordinates
import DimensionFourDependence.PrimitiveTwoAxisQuasiTranslation
import DimensionFourDependence.PrimitiveHomogeneousQuasiTranslationRank
import DimensionFourDependence.OriginalRankThreeQuasiTranslationReduction

/-! # Reduction of the positive-direction classification to a constant span bound -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

/-- The small-span conclusion alone now suffices in the positive
direction branch. The actual inverse coordinates, zero first two
entries, and binary dependence of the other entries are all constructed. -/
theorem primitive_positive_zero_acceleration_kernel_small_component_span_forces_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (u : Fin 4 → R₀) {e : ℕ}
    (hu : IsPrimRightKernel (jac H) u e) (he : 0 < e) (hacc : jac u *ᵥ u = 0)
    (hspan : finrank K (Submodule.span K (Set.range u)) ≤ 2) : ComponentsDependent H := by
  obtain ⟨r, s, hli, hr, hs⟩ :=
    component_span_at_most_two_constructs_independent_constant_relations u hspan
  obtain ⟨T, S, A, B, hTS, hST, hform⟩ :=
    two_independent_constant_relations_construct_two_axis_conjugacy u r s hli hr hs
  exact primitive_positive_zero_acceleration_kernel_in_two_axis_coordinates_forces_original_componentsDependent
    H hd hH hN u hu he hacc T S hTS hST A B hform

/-- Any positive-degree primitive zero-acceleration kernel of a
hypothetical independent original map has rank exactly two and its
components span at least three original constant dimensions. -/
theorem independent_nilpotent_map_positive_zero_acceleration_kernel_has_rank_two_and_large_span
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ComponentsDependent H)
    (u : Fin 4 → R₀) {e : ℕ} (hu : IsPrimRightKernel (jac H) u e)
    (he : 0 < e) (hacc : jac u *ᵥ u = 0) :
    polyRank (jac u) = 2 ∧ 3 ≤ finrank K (Submodule.span K (Set.range u)) := by
  refine ⟨primitive_positive_homogeneous_quasi_translation_rank_two
    u he hu.ne_zero hu.homog hu.prim hacc, ?_⟩
  by_contra hn
  exact hind (primitive_positive_zero_acceleration_kernel_small_component_span_forces_componentsDependent
    H hd hH hN u hu he hacc (by omega))

variable [IsAlgClosed K]

/-- Native reduction of any remaining original rank-three
counterexample: it constructs either a degree-zero primitive kernel,
or a primitive positive homogeneous quasi-translation of rank two
whose component span has dimension at least three. This last alternative
is precisely the one excluded by `PrimitiveGordanNoetherSpan`; no
classification result is assumed or introduced as an axiom. -/
theorem original_independent_rank_three_map_constructs_constant_kernel_or_large_span_rank_two_direction
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) :
    ∃ (u : Fin 4 → R₀) (e : ℕ), IsPrimRightKernel (jac H) u e ∧ jac u *ᵥ u = 0 ∧
      (e = 0 ∨ (0 < e ∧ polyRank (jac u) = 2 ∧
        3 ≤ finrank K (Submodule.span K (Set.range u)))) := by
  obtain ⟨u, e, hu, hacc⟩ :=
    original_independent_rank_three_map_constructs_zero_acceleration_kernel H hd hH hN hrank hind
  refine ⟨u, e, hu, hacc, ?_⟩
  by_cases he : e = 0
  · exact Or.inl he
  · exact Or.inr ⟨Nat.pos_of_ne_zero he,
      independent_nilpotent_map_positive_zero_acceleration_kernel_has_rank_two_and_large_span
        H hd hH hN hind u hu (Nat.pos_of_ne_zero he) hacc⟩

end DimensionFourDependence
