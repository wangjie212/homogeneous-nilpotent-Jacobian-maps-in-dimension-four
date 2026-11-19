import DimensionFourDependence.AffineLineDerivation

/-! # A varying planar tangent spans its fixed direction plane -/

namespace DimensionFourDependence

open Matrix Module

variable {F : Type*} [Field F] {n : ℕ}

/-- Two independent vectors inside a plane span that plane, so a
covector killing both kills its two prescribed direction generators. -/
theorem normal_kills_plane_of_independent_tangents
    (ν s t v w : Fin n → F) (hst : LinearIndependent F ![s, t])
    (hs : s ∈ Submodule.span F (Set.range ![v, w]))
    (ht : t ∈ Submodule.span F (Set.range ![v, w]))
    (hνs : ν ⬝ᵥ s = 0) (hνt : ν ⬝ᵥ t = 0) : ν ⬝ᵥ v = 0 ∧ ν ⬝ᵥ w = 0 := by
  have hle : Submodule.span F (Set.range ![s, t]) ≤ Submodule.span F (Set.range ![v, w]) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> assumption
  have hdim : finrank F (Submodule.span F (Set.range ![s, t])) = 2 := by
    simpa using finrank_span_eq_card hst
  have hbound : finrank F (Submodule.span F (Set.range ![v, w])) ≤ 2 := by
    exact finrank_range_le_card (R := F) ![v, w]
  have heq : Submodule.span F (Set.range ![s, t]) = Submodule.span F (Set.range ![v, w]) := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    have hm := Submodule.finrank_mono hle
    omega
  have hker : Submodule.span F (Set.range ![s, t]) ≤
      LinearMap.ker ((dotProductBilin F F) ν) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> assumption
  rw [heq] at hker
  exact ⟨hker (Submodule.subset_span ⟨0, rfl⟩), hker (Submodule.subset_span ⟨1, rfl⟩)⟩

variable {K : Type*} [Field K] [Algebra K F]

/-- Differentiating a vector in a fixed constant plane keeps it in that plane. -/
theorem derivation_mem_constant_plane (D : Derivation K F F) (v w : Fin n → K)
    (u : Fin n → F)
    (hu : u ∈ Submodule.span F (Set.range
      ![(fun i => algebraMap K F (v i)), (fun i => algebraMap K F (w i))])) :
    (fun i => D (u i)) ∈ Submodule.span F (Set.range
      ![(fun i => algebraMap K F (v i)), (fun i => algebraMap K F (w i))]) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := F)).mp hu
  apply (Submodule.mem_span_range_iff_exists_fun (R := F)).mpr
  refine ⟨fun i => D (c i), ?_⟩
  funext k
  have he := congrArg D (congrFun hc k)
  simpa [Fin.sum_univ_two, Pi.smul_apply, D.leibniz, smul_eq_mul, mul_comm] using he

/-- A constant normal killing a varying tangent in a fixed plane
annihilates the entire constant direction plane. -/
theorem constant_normal_kills_planar_tangent_space (D : Derivation K F F)
    (ν u : Fin n → F) (hν : ∀ i, D (ν i) = 0) (hνu : ν ⬝ᵥ u = 0)
    (v w : Fin n → K)
    (hu : u ∈ Submodule.span F (Set.range
      ![(fun i => algebraMap K F (v i)), (fun i => algebraMap K F (w i))]))
    (hvar : LinearIndependent F ![(fun i => D (u i)), u]) :
    ν ⬝ᵥ (fun i => algebraMap K F (v i)) = 0 ∧
      ν ⬝ᵥ (fun i => algebraMap K F (w i)) = 0 := by
  exact normal_kills_plane_of_independent_tangents ν _ u _ _ hvar
    (derivation_mem_constant_plane D v w u hu) hu
    (constant_normal_kills_derived_direction D ν u hν hνu) hνu

end DimensionFourDependence
