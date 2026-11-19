import DimensionFourDependence.ClosedPolynomialCurveParameter
import DimensionFourDependence.ClosedFieldTernaryAlgebraicPair

/-! # A normalized closed polynomial parameter for the dependent outputs -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 1800000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "O" => (aeval (fun _ : Fin 3 => (0 : K)))

/-- The dependent first and last outputs are polynomials in a common
parameter vanishing at the source origin. Its rational function field
is relatively algebraically closed in the actual source field. -/
theorem ternary_algebraic_pair_has_normalized_closed_polynomial_parameter
    (H : Fin 3 → R₃) (h₀ : ∀ i, O (H i) = 0)
    (hTrans : Transcendental K (ι (H 0)))
    (hAlg : IsAlgebraic (IntermediateField.adjoin K {ι (H 0)}) (ι (H 2))) :
    ∃ (r : R₃) (f g : Polynomial K),
      0 < r.totalDegree ∧ O r = 0 ∧ f.eval 0 = 0 ∧ g.eval 0 = 0 ∧
      H 0 = Polynomial.aeval r f ∧ H 2 = Polynomial.aeval r g ∧
      algebraicClosure (IntermediateField.adjoin K {ι r}) F = ⊥ := by
  let J : Fin 2 → R₃ := ![H 0, H 2]
  let Z : Fin 1 → F := fun _ => ι (H 0)
  have hZ : Set.range Z = {ι (H 0)} := by simp [Z, Set.range_const]
  have hZi : AlgebraicIndependent K Z :=
    (algebraicIndependent_singleton_iff 0).mpr hTrans
  have hZJ : Set.range Z ⊆ Set.range (fun i => ι (J i)) := by
    rintro a ⟨i, rfl⟩
    exact ⟨0, rfl⟩
  have hJA (i : Fin 2) : IsAlgebraic (IntermediateField.adjoin K (Set.range Z)) (ι (J i)) := by
    rw [hZ]
    fin_cases i
    · let B := IntermediateField.adjoin K {ι (H 0)}
      let j : B := ⟨ι (H 0), IntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩
      exact isAlgebraic_algebraMap (A := F) j
    · exact hAlg
  obtain ⟨r₀, P, hd, hP, hc⟩ := polynomial_curve_outputs_have_common_closed_polynomial_parameter
    Fin.castSuccEmb J (outputField_trdeg_of_independent_algebraic_generators Z hZi _ hZJ hJA)
  let c := O r₀
  let r := r₀ - C c
  let q : Polynomial K := Polynomial.X + Polynomial.C c
  have hr : r + C c = r₀ := sub_add_cancel _ _
  have hrd : 0 < r.totalDegree := by
    have he := totalDegree_sub_C_le r (-c)
    rw [map_neg, sub_neg_eq_add, hr] at he
    exact hd.trans_le he
  have hr₀ : O r = 0 := by simp [r, c]
  have hEval (i : Fin 2) : J i = Polynomial.aeval r ((P i).comp q) := by
    rw [Polynomial.aeval_comp, hP i]
    have hq : Polynomial.aeval r q = r₀ := by
      simpa only [q, map_add, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_eq] using hr
    rw [hq]
  have hf₀ (i : Fin 2) : ((P i).comp q).eval 0 = 0 := by
    have he := congrArg O (hEval i)
    rw [← Polynomial.aeval_algHom_apply, hr₀, Polynomial.aeval_def, Algebra.algebraMap_self] at he
    have hz : O (J i) = 0 := by
      fin_cases i
      · exact h₀ 0
      · exact h₀ 2
    simpa only [hz, Polynomial.eval₂_id] using he.symm
  have hSub : ι r = ι r₀ - algebraMap K F c := by
    change ι (r₀ - C c) = _
    rw [map_sub, ← algebraMap_eq, ← IsScalarTower.algebraMap_apply K R₃ F]
  have hEq : IntermediateField.adjoin K {ι r} = IntermediateField.adjoin K {ι r₀} := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ (rfl : _ = _)
      rw [hSub]
      exact sub_mem (IntermediateField.subset_adjoin K _ (Set.mem_singleton _))
        (IntermediateField.algebraMap_mem _ _)
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ (rfl : _ = _)
      have he : ι r₀ = ι r + algebraMap K F c := by rw [hSub, sub_add_cancel]
      rw [he]
      exact add_mem (IntermediateField.subset_adjoin K _ (Set.mem_singleton _))
        (IntermediateField.algebraMap_mem _ _)
  refine ⟨r, (P 0).comp q, (P 1).comp q, hrd, hr₀, hf₀ 0, hf₀ 1, hEval 0, hEval 1, ?_⟩
  rw [hEq, hc]
  exact algebraicClosure.algebraicClosure_eq_bot _ _

end DimensionFourDependence
