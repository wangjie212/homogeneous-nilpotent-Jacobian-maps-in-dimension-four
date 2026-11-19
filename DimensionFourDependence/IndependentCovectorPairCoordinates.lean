import DimensionFourDependence.PointAdaptedCoordinates
import DimensionFourDependence.LinearPolynomialConjugacy

/-! # Two independent constant relations construct actual inverse coordinates -/

namespace DimensionFourDependence

open Matrix Module MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]

/-- Any two independent covectors become the first two actual rows
of an invertible coordinate matrix, with its inverse constructed. -/
theorem independent_covector_pair_constructs_inverse_coordinate_matrices
    (r s : Fin 4 → K) (hli : LinearIndependent K ![r, s]) :
    ∃ T S : Matrix (Fin 4) (Fin 4) K, T * S = 1 ∧ S * T = 1 ∧
      (∀ j, S 0 j = r j) ∧ (∀ j, S 1 j = s j) := by
  classical
  let v : Fin 2 → (Fin 4 → K) := ![r, s]
  let w : Fin 2 → (Fin 4 → K) := fun i => Pi.single (i.castAdd 2) 1
  have hw : LinearIndependent K w :=
    (Pi.linearIndependent_single_one (Fin 4) K).comp (Fin.castAdd 2) (by
      intro i j hij
      exact Fin.ext (congrArg (fun k : Fin 4 => k.val) hij))
  let er := hli.linearCombinationEquiv
  let ew := hw.linearCombinationEquiv
  let f := er.symm.trans ew
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hsend (i : Fin 2) : g (v i) = w i := by
    have he := hg (er (Finsupp.single i 1))
    have hf : f (er (Finsupp.single i 1)) = ew (Finsupp.single i 1) := by simp [f]
    rw [hf] at he
    simpa only [er, ew, LinearIndependent.linearCombinationEquiv_apply_coe,
      Finsupp.linearCombination_single, one_smul] using he.symm
  let A := LinearMap.toMatrix' g.toLinearMap
  let B := LinearMap.toMatrix' g.symm.toLinearMap
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have heq : g.toLinearMap.comp g.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact g.apply_symm_apply x
    rw [heq, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have heq : g.symm.toLinearMap.comp g.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact g.symm_apply_apply x
    rw [heq, LinearMap.toMatrix'_id]
  have hBsend (i : Fin 2) : B *ᵥ w i = v i := by
    change Matrix.toLin' (LinearMap.toMatrix' g.symm.toLinearMap) (w i) = _
    rw [Matrix.toLin'_toMatrix', ← hsend]
    exact g.symm_apply_apply (v i)
  have hrow (i : Fin 2) (j : Fin 4) : B j (i.castAdd 2) = v i j := by
    have he := congrFun (hBsend i) j
    simp only [w, Matrix.mulVec_single_one] at he
    exact he
  refine ⟨Aᵀ, Bᵀ, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]
  · intro j
    exact hrow 0 j
  · intro j
    exact hrow 1 j

/-- A two-dimensional bound on the actual component span constructs
two independent original constant relations, without an assumed choice
of rows or coordinate matrices. -/
theorem component_span_at_most_two_constructs_independent_constant_relations
    (u : Fin 4 → MvPolynomial (Fin 4) K)
    (hspan : finrank K (Submodule.span K (Set.range u)) ≤ 2) :
    ∃ r s : Fin 4 → K, LinearIndependent K ![r, s] ∧
      (∑ j, r j • u j) = 0 ∧ (∑ j, s j • u j) = 0 := by
  let L := Fintype.linearCombination K u
  have hdim := LinearMap.finrank_range_add_finrank_ker L
  have hrange : finrank K (LinearMap.range L) ≤ 2 := by
    rw [Fintype.range_linearCombination]
    exact hspan
  have hker : 2 ≤ finrank K (LinearMap.ker L) := by
    simp only [Module.finrank_pi, Fintype.card_fin] at hdim
    omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hker
  have hv' : LinearIndependent K (fun i : Fin 2 => (v i : Fin 4 → K)) :=
    hv.map' (f := (LinearMap.ker L).subtype) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have heq : (fun i : Fin 2 => (v i : Fin 4 → K)) = ![(v 0 : Fin 4 → K), (v 1 : Fin 4 → K)] := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at hv'
  refine ⟨v 0, v 1, hv', ?_, ?_⟩
  · exact (v 0).property
  · exact (v 1).property

/-- The two actual relations construct the full original-source
conjugacy with its first two direction entries identically zero. -/
theorem two_independent_constant_relations_construct_two_axis_conjugacy
    (u : Fin 4 → MvPolynomial (Fin 4) K) (r s : Fin 4 → K)
    (hli : LinearIndependent K ![r, s])
    (hr : (∑ j, r j • u j) = 0) (hs : (∑ j, s j • u j) = 0) :
    ∃ (T S : Matrix (Fin 4) (Fin 4) K) (A B : MvPolynomial (Fin 4) K),
      T * S = 1 ∧ S * T = 1 ∧ linearPolynomialConjugate T S u = ![0, 0, A, B] := by
  obtain ⟨T, S, hTS, hST, hrow0, hrow1⟩ :=
    independent_covector_pair_constructs_inverse_coordinate_matrices r s hli
  have hz (i : Fin 4) (c : Fin 4 → K) (hrow : ∀ j, S i j = c j)
      (hrel : (∑ j, c j • u j) = 0) : linearPolynomialConjugate T S u i = 0 := by
    have he := congrArg (linearPolynomialPullback T) hrel
    simpa only [linearPolynomialConjugate, hrow, linearPolynomialPullback, map_sum, map_smul, map_zero,
      MvPolynomial.smul_eq_C_mul, map_mul, aeval_C, MvPolynomial.algebraMap_eq] using he
  have hz0 := hz 0 r hrow0 hr
  have hz1 := hz 1 s hrow1 hs
  refine ⟨T, S, linearPolynomialConjugate T S u 2, linearPolynomialConjugate T S u 3,
    hTS, hST, ?_⟩
  funext i
  fin_cases i <;> simp [hz0, hz1]

end DimensionFourDependence
