import DimensionFourDependence.ConstantKernelSourceReduction

/-! # Constant component relations lift from the smaller actual source map -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] {n : ℕ}

/-- A constant relation among the first n smaller-source forms lifts
to the full transformed tuple and then to the original map. -/
theorem smaller_source_leading_relation_forces_original_componentsDependent
    (H : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (T S : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hTS : T * S = 1) (hST : S * T = 1)
    (G : Fin (n + 1) → MvPolynomial (Fin n) K)
    (hG : ∀ i, rename Fin.castSucc (G i) = linearPolynomialConjugate T S H i)
    (hdep : ComponentsDependent (fun i : Fin n => G i.castSucc)) :
    ComponentsDependent H := by
  classical
  by_contra hind
  apply linearPolynomialConjugate_componentsIndependent T S hTS hST H hind
  obtain ⟨c, hc, hrel⟩ := hdep
  let b : Fin (n + 1) → K := Fin.lastCases 0 c
  have hb : b ≠ 0 := by
    intro hz
    apply hc
    funext i
    simpa only [b, Fin.lastCases_castSucc, Pi.zero_apply] using congrFun hz i.castSucc
  refine ⟨b, hb, ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp only [b, Fin.lastCases_last, zero_smul, add_zero, Fin.lastCases_castSucc]
  have he := congrArg (rename Fin.castSucc :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1)) K) hrel
  simpa only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, rename_C, map_zero, hG] using he

/-- A hypothetical independent original map therefore produces an
independent leading smaller-source map in every constructed coordinate
reduction. -/
theorem original_independence_forces_smaller_source_leading_independence
    (H : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hind : ¬ComponentsDependent H)
    (T S : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hTS : T * S = 1) (hST : S * T = 1)
    (G : Fin (n + 1) → MvPolynomial (Fin n) K)
    (hG : ∀ i, rename Fin.castSucc (G i) = linearPolynomialConjugate T S H i) :
    ¬ComponentsDependent (fun i : Fin n => G i.castSucc) :=
  fun hdep => hind (smaller_source_leading_relation_forces_original_componentsDependent
    H T S hTS hST G hG hdep)

variable [CharZero K]

/-- The homogeneous rank-one dependence argument works in every
dimension at least two. No nilpotence or classification is needed. -/
theorem positive_homogeneous_rank_at_most_one_componentsDependent
    (hn : 2 ≤ n) (H : Fin n → MvPolynomial (Fin n) K) {d : ℕ}
    (hd : 0 < d) (hH : IsHomogMap H d) (hr : polyRank (jac H) ≤ 1) :
    ComponentsDependent H := by
  classical
  letI : NeZero n := ⟨by omega⟩
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  by_cases hzero : H = 0
  · subst H
    exact ⟨fun _ => 1, by simp [funext_iff], by simp⟩
  obtain ⟨i, hi⟩ : ∃ i, H i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hzero
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨c, hc⟩ := lemma_2_1_rank_le_one H hd hH hr i j hi
  refine ⟨Pi.single j 1 - c • Pi.single i 1, ?_, ?_⟩
  · intro hz
    have h := congrFun hz j
    simp [Pi.single_apply, hji] at h
  · simp [sub_smul, Finset.sum_sub_distrib, Pi.single_apply,
      Finset.sum_ite_eq', hc]

/-- The precise assembly step for the constant-direction branch. The
only remaining input is the full smaller-dimensional dependence theorem;
the original direction constructs all coordinates, forms and nilpotence
hypotheses required to apply that theorem. -/
theorem homogeneous_constant_kernel_dependence_of_smaller_dimension_dependence
    (hsmall : ∀ (d : ℕ), 0 < d →
      ∀ G : Fin n → MvPolynomial (Fin n) K,
        IsHomogMap G d → IsNilpotent (jac G) → ComponentsDependent G)
    (H : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) {d : ℕ}
    (hd : 0 < d) (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (c : Fin (n + 1) → K) (hc : c ≠ 0)
    (hker : jac H *ᵥ (fun i => C (c i)) = 0) : ComponentsDependent H := by
  obtain ⟨T, S, G, hTS, hST, hG, hhom, hnil⟩ :=
    homogeneous_nilpotent_constant_kernel_constructs_smaller_source_map H hH hN c hc hker
  exact smaller_source_leading_relation_forces_original_componentsDependent H T S hTS hST G hG
    (hsmall d hd (fun i : Fin n => G i.castSucc) (fun i => hhom i.castSucc) hnil)

end DimensionFourDependence
