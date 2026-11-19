import DimensionFourDependence.PrimeConstantCovectorDimension

/-! # Small actual covector spaces admit independent two-plane covers -/

namespace DimensionFourDependence

open Matrix Module

set_option maxHeartbeats 3500000

variable {K : Type*} [Field K]

/-- Every actual subspace of original four-dimensional covectors
of dimension at most two is contained in a plane spanned by an actual
independent pair, including subspaces of dimension zero or one. -/
theorem covector_space_finrank_le_two_constructs_independent_covering_pair
    (W : Submodule K (Fin 4 → K)) (hW : finrank K W ≤ 2) :
    ∃ μ ν : Fin 4 → K, LinearIndependent K ![μ, ν] ∧
      W ≤ Submodule.span K ({μ, ν} : Set (Fin 4 → K)) := by
  classical
  let r := finrank K W
  let b := Module.finBasis K W
  let v : Fin r → (Fin 4 → K) := fun i => b i
  have hv : LinearIndependent K v := b.linearIndependent.map' W.subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hr4 : r ≤ 4 := by dsimp only [r]; omega
  let e : Fin r ↪ Fin 4 :=
    ⟨Fin.castLE hr4, by intro i j h; exact Fin.ext (congrArg (fun k : Fin 4 => k.val) h)⟩
  obtain ⟨T, S, hTS, hST, hcol⟩ := independent_vector_family_constructs_inverse_coordinate_columns v hv e
  let μ : Fin 4 → K := fun i => T i 0
  let ν : Fin 4 → K := fun i => T i 1
  have hinj : Function.Injective (Matrix.toLin' T) := by
    intro x y hxy
    have he := congrArg (fun z => S *ᵥ z) hxy
    simpa only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hST, Matrix.one_mulVec] using he
  have hstd : LinearIndependent K (fun j : Fin 2 =>
      (Pi.single ((![0, 1] : Fin 2 → Fin 4) j) (1 : K) : Fin 4 → K)) :=
    (Pi.linearIndependent_single_one (Fin 4) K).comp (![0, 1] : Fin 2 → Fin 4) (by decide)
  have hpair : LinearIndependent K ![μ, ν] := by
    have hi := hstd.map' (Matrix.toLin' T) (LinearMap.ker_eq_bot.mpr hinj)
    convert hi using 1
    funext j
    fin_cases j <;> simp [μ, ν, Matrix.toLin'_apply] <;> rfl
  let M := Submodule.span K ({μ, ν} : Set (Fin 4 → K))
  have hbm (j : Fin r) : (b j : Fin 4 → K) ∈ M := by
    have hj : j.val = 0 ∨ j.val = 1 := by have hjlt := j.isLt; dsimp only [r] at hjlt; omega
    rcases hj with hj | hj
    · have he : e j = 0 := Fin.ext hj
      have hbμ : (b j : Fin 4 → K) = μ := by
        funext i
        exact (he ▸ hcol j i).symm
      rw [hbμ]
      exact Submodule.subset_span (by simp)
    · have he : e j = 1 := Fin.ext hj
      have hbν : (b j : Fin 4 → K) = ν := by
        funext i
        exact (he ▸ hcol j i).symm
      rw [hbν]
      exact Submodule.subset_span (by simp)
  have hle : Submodule.span K (Set.range b) ≤ M.comap W.subtype := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    exact hbm j
  refine ⟨μ, ν, hpair, ?_⟩
  intro w hw
  exact hle (show (⟨w, hw⟩ : W) ∈ Submodule.span K (Set.range b) by rw [b.span_eq]; trivial)

/-- The entire constant-linear-form space of an actual height-two
source prime is contained in an actual independent covector plane. -/
theorem height_le_two_prime_constructs_independent_covector_covering_plane
    (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime] (hQ : Q.height ≤ 2) :
    ∃ μ ν : Fin 4 → K, LinearIndependent K ![μ, ν] ∧
      ∀ w : Fin 4 → K, linearFormPolynomial w ∈ Q →
        w ∈ Submodule.span K ({μ, ν} : Set (Fin 4 → K)) := by
  obtain ⟨μ, ν, hμν, hle⟩ := covector_space_finrank_le_two_constructs_independent_covering_pair
    (idealConstantCovectorSpace Q) (height_le_two_prime_constant_covector_space_finrank_le_two Q hQ)
  exact ⟨μ, ν, hμν, fun w hw => hle ((mem_idealConstantCovectorSpace_iff Q w).mpr hw)⟩

end DimensionFourDependence
