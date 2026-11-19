import DimensionFourDependence.FiniteParameterGraphRuling
import DimensionFourDependence.GraphRulingCovectorProjection

/-! # The actual algebraic graph dual pair constructs a common finite ruling field -/

namespace DimensionFourDependence

open Matrix Module

set_option maxHeartbeats 1000000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- All four specified algebraic coefficient vectors descend to
one finite intermediate field, retaining their original coordinates,
graph ruling membership and dual values. Independence of the finite
root-form restrictions is a conclusion, not a supplied hypothesis. -/
theorem algebraic_graph_dual_pair_constructs_same_finite_ruling_field
    (p : RatFunc K →ₐ[K] F) (A : Fin 3 → RatFunc K) (m s b a : Fin 3 → F)
    (hm : ∀ i, IsAlgebraic p.fieldRange (m i)) (hs : ∀ i, IsAlgebraic p.fieldRange (s i))
    (hb : ∀ i, IsAlgebraic p.fieldRange (b i)) (ha : ∀ i, IsAlgebraic p.fieldRange (a i))
    (hbW : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ b = 0)
    (haW : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ a = 0)
    (hmb : m ⬝ᵥ b = 1) (hsb : s ⬝ᵥ b = 0) (hma : m ⬝ᵥ a = 0) (hsa : s ⬝ᵥ a = 1) :
    ∃ C : IntermediateField p.fieldRange F, Module.Finite p.fieldRange C ∧
      ∃ mC sC bC aC : Fin 3 → C,
        (∀ i, (mC i : F) = m i) ∧ (∀ i, (sC i : F) = s i) ∧
        (∀ i, (bC i : F) = b i) ∧ (∀ i, (aC i : F) = a i) ∧
        bC ∈ finiteParameterGraphRuling p C A ∧ aC ∈ finiteParameterGraphRuling p C A ∧
        mC ⬝ᵥ bC = 1 ∧ sC ⬝ᵥ bC = 0 ∧ mC ⬝ᵥ aC = 0 ∧ sC ⬝ᵥ aC = 1 ∧
        LinearIndependent C ![rulingFormRestriction (finiteParameterGraphRuling p C A) mC,
          rulingFormRestriction (finiteParameterGraphRuling p C A) sC] := by
  classical
  let U : Set F := ((Set.range m ∪ Set.range s) ∪ Set.range b) ∪ Set.range a
  have hU : U.Finite := (((Set.finite_range m).union (Set.finite_range s)).union
    (Set.finite_range b)).union (Set.finite_range a)
  letI : Fintype U := hU.fintype
  let C := IntermediateField.adjoin p.fieldRange U
  have hfinite : Module.Finite p.fieldRange C := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro x (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact (hm i).isIntegral
    · exact (hs i).isIntegral
    · exact (hb i).isIntegral
    · exact (ha i).isIntegral
  let mC : Fin 3 → C := fun i => ⟨m i, IntermediateField.subset_adjoin _ _
    (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩)))⟩
  let sC : Fin 3 → C := fun i => ⟨s i, IntermediateField.subset_adjoin _ _
    (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))⟩
  let bC : Fin 3 → C := fun i => ⟨b i, IntermediateField.subset_adjoin _ _ (Or.inl (Or.inr ⟨i, rfl⟩))⟩
  let aC : Fin 3 → C := fun i => ⟨a i, IntermediateField.subset_adjoin _ _ (Or.inr ⟨i, rfl⟩)⟩
  have hbC : bC ∈ finiteParameterGraphRuling p C A := by
    change finiteParameterGraphNormal p C A ⬝ᵥ bC = 0
    apply (algebraMap C F).injective
    simpa only [dotProduct, map_sum, map_mul, map_zero, IntermediateField.algebraMap_apply,
      finiteParameterGraphNormal_value] using hbW
  have haC : aC ∈ finiteParameterGraphRuling p C A := by
    change finiteParameterGraphNormal p C A ⬝ᵥ aC = 0
    apply (algebraMap C F).injective
    simpa only [dotProduct, map_sum, map_mul, map_zero, IntermediateField.algebraMap_apply,
      finiteParameterGraphNormal_value] using haW
  have hmbC : mC ⬝ᵥ bC = 1 := by
    apply (algebraMap C F).injective
    simpa only [dotProduct, map_sum, map_mul, map_one, IntermediateField.algebraMap_apply] using hmb
  have hsbC : sC ⬝ᵥ bC = 0 := by
    apply (algebraMap C F).injective
    simpa only [dotProduct, map_sum, map_mul, map_zero, IntermediateField.algebraMap_apply] using hsb
  have hmaC : mC ⬝ᵥ aC = 0 := by
    apply (algebraMap C F).injective
    simpa only [dotProduct, map_sum, map_mul, map_zero, IntermediateField.algebraMap_apply] using hma
  have hsaC : sC ⬝ᵥ aC = 1 := by
    apply (algebraMap C F).injective
    simpa only [dotProduct, map_sum, map_mul, map_one, IntermediateField.algebraMap_apply] using hsa
  exact ⟨C, hfinite, mC, sC, bC, aC, (fun _ => rfl), (fun _ => rfl), (fun _ => rfl),
    (fun _ => rfl), hbC, haC, hmbC, hsbC, hmaC, hsaC,
    ruling_form_pair_independent_of_specified_dual_values (finiteParameterGraphRuling p C A)
      mC sC bC aC hbC haC hmbC hsbC hmaC hsaC⟩

end DimensionFourDependence
