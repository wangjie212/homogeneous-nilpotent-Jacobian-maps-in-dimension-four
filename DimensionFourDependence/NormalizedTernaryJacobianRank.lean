import DimensionFourDependence.ClosedPolynomialCurveParameter
import DimensionFourDependence.RankOnePolynomialParameterDependence
import DimensionFourDependence.RationalJacobianCriterion

/-! # Independent normalized ternary outputs force rank two -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 1700000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)

/-- The rank-one case of the ternary classification is impossible for
normalized independent outputs: their relatively closed field has a
common polynomial generator, and the exact trace forces a relation. -/
theorem closed_field_normalized_independent_ternary_nilpotent_rank_two
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hind : ¬ComponentsDependent H) (hN : IsNilpotent (jac H)) :
    polyRank (jac H) = 2 := by
  let Q : Fin 3 → F := fun i => ι (H i)
  let B := IntermediateField.adjoin K (Set.range Q)
  have htrdeg : Algebra.trdeg K B = (polyRank (jac H) : Cardinal) := by
    change Algebra.trdeg K (IntermediateField.adjoin K (Set.range Q)) = _
    rw [rationalJacobian_rank_eq_output_trdeg Q, rationalJacobian_polynomial H]
    rfl
  have hle := polyRank_lt_of_isNilpotent (jac H) hN (by norm_num)
  have hr0 : polyRank (jac H) ≠ 0 := by
    intro hr
    have ht : Algebra.trdeg K B = 0 := by rw [htrdeg, hr, Nat.cast_zero]
    let : Algebra.IsAlgebraic K B := trdeg_eq_zero_iff.mp ht
    let u : B := ⟨Q 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B)).2 u
    have hcF : ι (H 0) = algebraMap K F c := by
      have he := congrArg B.val hc
      rw [AlgHom.commutes] at he
      exact he.symm
    have hH : H 0 = C c := by
      apply IsFractionRing.injective R₃ F
      rw [hcF, ← algebraMap_eq, ← IsScalarTower.algebraMap_apply K R₃ F]
    have hc0 : c = 0 := by
      have ho := h0 0
      rwa [hH, aeval_C, Algebra.algebraMap_self_apply] at ho
    have hz : H 0 = 0 := by rw [hH, hc0, map_zero]
    apply hind
    refine ⟨![1,0,0], ?_, ?_⟩
    · intro h
      exact one_ne_zero (congrFun h (0 : Fin 3))
    · simp [Fin.sum_univ_three, hz]
  have hr1 : polyRank (jac H) ≠ 1 := by
    intro hr
    have ht : Algebra.trdeg K B = 1 := by rw [htrdeg, hr, Nat.cast_one]
    let j : Fin 3 ↪ Fin 4 := ⟨Fin.castSucc, Fin.castSucc_injective 3⟩
    obtain ⟨T, A, hT, hA, _⟩ := polynomial_curve_outputs_have_common_closed_polynomial_parameter j H ht
    exact hind (normalized_polynomial_parameter_map_trace_zero_componentsDependent H h0 T hT A hA
      (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero)
  omega

end DimensionFourDependence
