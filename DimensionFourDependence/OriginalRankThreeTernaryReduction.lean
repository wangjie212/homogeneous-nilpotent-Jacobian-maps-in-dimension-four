import DimensionFourDependence.PrimitiveQuasiTranslationClassification
import DimensionFourDependence.SmallerSourceDependenceTransport

/-! # The remaining rank-three case constructs a genuine ternary counterexample -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "A₀" => MvPolynomial (Fin 3) K

/-- A remaining independent original rank-three map constructs inverse
constant coordinates and four actual ternary forms. Their leading
three-component map is homogeneous of the same degree, independent,
nilpotent and of rank exactly two. Every auxiliary datum is constructed
from the original hypotheses; the ternary dependence theorem itself is
not assumed here. -/
theorem original_independent_rank_three_map_constructs_independent_ternary_nilpotent_map
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (hind : ¬ComponentsDependent H) :
    2 ≤ d ∧ ∃ (T S : Matrix (Fin 4) (Fin 4) K) (G : Fin 4 → A₀),
      T * S = 1 ∧ S * T = 1 ∧
      (∀ i, rename Fin.castSucc (G i) = linearPolynomialConjugate T S H i) ∧
      (∀ i, (G i).IsHomogeneous d) ∧
      IsNilpotent (jac (fun i : Fin 3 => G i.castSucc)) ∧
      ¬ComponentsDependent (fun i : Fin 3 => G i.castSucc) ∧
      polyRank (jac (fun i : Fin 3 => G i.castSucc)) = 2 := by
  have hd2 : 2 ≤ d := by
    by_contra hn
    have hd1 : d = 1 := by omega
    exact hind (dependence_degree_one H (hd1 ▸ hH) hN)
  obtain ⟨c, hc, hker⟩ :=
    original_independent_rank_three_map_constructs_nonzero_constant_right_kernel
      H hd hH hN hrank hind
  obtain ⟨T, S, G, hTS, hST, hG, hhom, hnil⟩ :=
    homogeneous_nilpotent_constant_kernel_constructs_smaller_source_map H hH hN c hc hker
  have hindG := original_independence_forces_smaller_source_leading_independence H hind T S hTS hST G hG
  have hrlt := polyRank_lt_of_isNilpotent (jac (fun i : Fin 3 => G i.castSucc)) hnil (by norm_num)
  have hrge : 2 ≤ polyRank (jac (fun i : Fin 3 => G i.castSucc)) := by
    by_contra hn
    exact hindG (positive_homogeneous_rank_at_most_one_componentsDependent (by norm_num)
      (fun i : Fin 3 => G i.castSucc) hd (fun i => hhom i.castSucc) (by omega))
  exact ⟨hd2, T, S, G, hTS, hST, hG, hhom, hnil, hindG, by omega⟩

/-- Once the homogeneous ternary dependence theorem is checked, the
entire original rank-three branch follows, without any additional
geometric or classification assumption. This theorem records the exact
remaining mathematical interface rather than asserting that input. -/
theorem original_rank_three_dependence_of_homogeneous_ternary_dependence
    (hternary : ∀ (d : ℕ), 0 < d → ∀ G : Fin 3 → A₀,
      IsHomogMap G d → IsNilpotent (jac G) → ComponentsDependent G)
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) :
    ComponentsDependent H := by
  by_contra hind
  obtain ⟨_hd2, T, S, G, _hTS, _hST, _hG, hhom, hnil, hindG, _hr⟩ :=
    original_independent_rank_three_map_constructs_independent_ternary_nilpotent_map
      H hd hH hN hrank hind
  exact hindG (hternary d hd (fun i : Fin 3 => G i.castSucc) (fun i => hhom i.castSucc) hnil)

end DimensionFourDependence
