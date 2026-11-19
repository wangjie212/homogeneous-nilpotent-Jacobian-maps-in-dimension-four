import DimensionFourDependence.RankSelectionOfIndependentOutputs
import DimensionFourDependence.LinearConjugacyEvaluationExtension
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-! # A simultaneous source and target permutation selects the independent pair -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 1900000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)

private noncomputable def ternaryPermutationMatrix (p : Equiv.Perm (Fin 3)) :
    Matrix (Fin 3) (Fin 3) K := fun i j => if p i = j then 1 else 0

omit [CharZero K] in
private theorem ternaryPermutationMatrix_mul_symm (p : Equiv.Perm (Fin 3)) :
    ternaryPermutationMatrix (K := K) p * ternaryPermutationMatrix p.symm = 1 := by
  ext i j
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (p i)]
  · simp [Matrix.one_apply, ternaryPermutationMatrix]
  · intro k _ hk
    simp [ternaryPermutationMatrix, Ne.symm hk]
  · simp

omit [CharZero K] in
private theorem ternaryPermutationConjugate_value (p : Equiv.Perm (Fin 3)) (H : Fin 3 → R₃)
    (i : Fin 3) :
    linearPolynomialConjugate (ternaryPermutationMatrix p.symm) (ternaryPermutationMatrix p) H i =
      linearPolynomialPullback (ternaryPermutationMatrix p.symm) (H (p i)) := by
  classical
  simp [linearPolynomialConjugate, ternaryPermutationMatrix, apply_ite]

/-- In a nilpotent chart with two independent outputs, the last output
belongs to the actual coefficient field of the pair. -/
theorem ternary_nilpotent_independent_pair_last_output_is_algebraic
    (H : Fin 3 → R₃) (hN : IsNilpotent (jac H))
    (hY : AlgebraicIndependent K (fun i : Fin 2 => ι (H i.castSucc))) :
    IsAlgebraic (IntermediateField.adjoin K (Set.range (fun i : Fin 2 => ι (H i.castSucc)))) (ι (H 2)) := by
  let Y : Fin 2 → F := fun i => ι (H i.castSucc)
  let B := IntermediateField.adjoin K (Set.range Y)
  let A := Algebra.adjoin K (Set.range Y)
  by_contra hn
  have ht : Transcendental A (ι (H 2)) := fun h =>
    hn (IntermediateField.isAlgebraic_adjoin_iff.mpr h)
  let e := finSuccEquiv' (Fin.last 2)
  let Z : Option (Fin 2) → F := fun i => i.elim (ι (H 2)) Y
  have hZ : AlgebraicIndependent K Z := (hY.option_iff_transcendental _).mpr ht
  have he : Z ∘ e = fun i : Fin 3 => ι (H i) := by
    funext i
    fin_cases i <;> rfl
  have hF : AlgebraicIndependent K (fun i : Fin 3 => ι (H i)) := by
    rw [← he]
    exact hZ.comp e e.injective
  have hR := rationalJacobian_rank_of_independent (fun i : Fin 3 => ι (H i)) hF
  rw [rationalJacobian_polynomial] at hR
  have hle := polyRank_lt_of_isNilpotent (jac H) hN (by norm_num)
  change polyRank (jac H) = 3 at hR
  omega

/-- One simultaneous permutation preserves normalization, independence
and nilpotence and puts an independent output pair in the first two slots. -/
theorem ternary_rank_two_constructs_normalized_independent_output_chart
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hind : ¬ComponentsDependent H) (hN : IsNilpotent (jac H)) (hR : polyRank (jac H) = 2) :
    ∃ T S : Matrix (Fin 3) (Fin 3) K, T * S = 1 ∧ S * T = 1 ∧
      let G := linearPolynomialConjugate T S H
      (∀ i, aeval (fun _ : Fin 3 => (0 : K)) (G i) = 0) ∧ ¬ComponentsDependent G ∧
      IsNilpotent (jac G) ∧ AlgebraicIndependent K (fun i : Fin 2 => ι (G i.castSucc)) := by
  let Q : Fin 3 → F := fun i => ι (H i)
  have hJ : (rationalJacobian Q).rank = 2 := by
    rw [show rationalJacobian Q = _ from rationalJacobian_polynomial H]
    exact hR
  obtain ⟨j, hj, hY, _⟩ := jacobian_rank_selects_independent_output_indices Q hJ
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair Fin.castSucc j (Fin.castSucc_injective 2) hj
  let T : Matrix (Fin 3) (Fin 3) K := ternaryPermutationMatrix p.symm
  let S : Matrix (Fin 3) (Fin 3) K := ternaryPermutationMatrix p
  have hTS : T * S = 1 := ternaryPermutationMatrix_mul_symm p.symm
  have hST : S * T = 1 := ternaryPermutationMatrix_mul_symm p
  let G := linearPolynomialConjugate T S H
  have hGn := linearPolynomialConjugate_nilpotent T S hTS hST H hN
  have hGi := linearPolynomialConjugate_componentsIndependent T S hTS hST H hind
  have hG0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (G i) = 0 := by
    have he := linearPolynomialConjugate_aeval_extension_eq_zero T S hTS H
      (fun _ : Fin 3 => (0 : K)) h0
    have hz : S.map (algebraMap K K) *ᵥ (fun _ : Fin 3 => (0 : K)) = 0 := mulVec_zero _
    rw [hz] at he
    exact he
  let φ := matrixSourceFractionEquiv T S hTS hST
  have hEq : (fun i : Fin 2 => ι (G i.castSucc)) = φ.toAlgHom ∘ (fun i => Q (j i)) := by
    funext i
    rw [show G i.castSucc = linearPolynomialPullback T (H (p i.castSucc)) from ternaryPermutationConjugate_value p H _,
      hp]
    exact (matrixSourceFractionEquiv_polynomial T S hTS hST _).symm
  refine ⟨T, S, hTS, hST, hG0, hGi, hGn, ?_⟩
  rw [hEq]
  exact hY.map' (f := φ.toAlgHom) φ.injective

end DimensionFourDependence
