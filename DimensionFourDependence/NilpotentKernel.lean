import DimensionFourDependence.Flag

/-! # The kernel direction of a nilpotent matrix of corank one -/

namespace DimensionFourDependence

open Matrix

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- A nonzero nilpotent operator has a nonzero vector in both its kernel
and its image. This uses the last nonzero step of a nilpotent chain. -/
theorem nilpotent_nonzero_kernel_image (f : Module.End F V)
    (hf : IsNilpotent f) (hf0 : f ≠ 0) : ∃ w : V, f w ≠ 0 ∧ f (f w) = 0 := by
  classical
  obtain ⟨m, hm⟩ := hf
  have hex : ∃ k : ℕ, f ^ (k + 2) = 0 :=
    ⟨m, by rw [pow_add, hm, zero_mul]⟩
  let k := Nat.find hex
  have hk : f ^ (k + 2) = 0 := Nat.find_spec hex
  have hprev : f ^ (k + 1) ≠ 0 := by
    intro h
    cases he : k with
    | zero => exact hf0 (by simpa [he] using h)
    | succ t =>
      have ht : t < Nat.find hex := by omega
      exact Nat.find_min hex ht (by simpa [he, Nat.add_assoc] using h)
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hprev
  refine ⟨(f ^ k) v, ?_, ?_⟩
  · simpa only [pow_succ', Module.End.mul_apply, LinearMap.zero_apply] using hv
  · have h := congrArg (fun g : Module.End F V => g v) hk
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ', pow_succ'] at h
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using h

/-- For a nilpotent operator with a one-dimensional kernel, every kernel
vector is in its image, provided the operator is nonzero. -/
theorem nilpotent_kernel_le_range [FiniteDimensional F V]
    (f : Module.End F V) (hf : IsNilpotent f) (hf0 : f ≠ 0)
    (hdim : Module.finrank F (LinearMap.ker f) = 1) :
    LinearMap.ker f ≤ LinearMap.range f := by
  obtain ⟨w, hw0, hw⟩ := nilpotent_nonzero_kernel_image f hf hf0
  let z : LinearMap.ker f := ⟨f w, hw⟩
  have hz : z ≠ 0 := by
    intro h
    exact hw0 (congrArg Subtype.val h)
  intro u hu
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' z hz).mp hdim ⟨u, hu⟩
  refine ⟨c • w, ?_⟩
  have he := congrArg Subtype.val hc
  simpa only [map_smul, Submodule.coe_smul_of_tower] using he

/-- A positive-rank nilpotent matrix has a nonzero right-kernel vector. -/
theorem matrix_nilpotent_exists_nonzero_kernel {n : ℕ}
    (N : Matrix (Fin n) (Fin n) F) (hN : IsNilpotent N) (hrank : 0 < N.rank) :
    ∃ u : Fin n → F, u ≠ 0 ∧ N *ᵥ u = 0 := by
  have hnil : IsNilpotent N.toLin' := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by rw [← Matrix.toLin'_pow, hk]; simp⟩
  have hN0 : N.toLin' ≠ 0 := by
    intro h
    have hzero : N.rank = 0 := by
      change Module.finrank F (LinearMap.range N.toLin') = 0
      rw [h, LinearMap.range_zero]
      exact finrank_bot F (Fin n → F)
    omega
  obtain ⟨w, hw0, hw⟩ := nilpotent_nonzero_kernel_image N.toLin' hnil hN0
  exact ⟨N *ᵥ w, hw0, hw⟩

/-- Matrix form of the corank-one kernel-image inclusion. -/
theorem matrix_nilpotent_kernel_in_image {n : ℕ}
    (N : Matrix (Fin n) (Fin n) F) (hN : IsNilpotent N)
    (hn : 2 ≤ n) (hrank : N.rank + 1 = n)
    (u : Fin n → F) (hu : N *ᵥ u = 0) : ∃ w, N *ᵥ w = u := by
  have hnil : IsNilpotent N.toLin' := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by rw [← Matrix.toLin'_pow, hk]; simp⟩
  have hr : Module.finrank F (LinearMap.range N.toLin') + 1 = n := hrank
  have hN0 : N.toLin' ≠ 0 := by
    intro h
    have hzero : Module.finrank F (LinearMap.range N.toLin') = 0 := by
      rw [h, LinearMap.range_zero]
      exact finrank_bot F (Fin n → F)
    omega
  have hd := LinearMap.finrank_range_add_finrank_ker N.toLin'
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  have hk : Module.finrank F (LinearMap.ker N.toLin') = 1 := by omega
  exact nilpotent_kernel_le_range N.toLin' hnil hN0 hk hu

/-- A left kernel covector kills every right kernel vector for a nilpotent
matrix of corank one in dimension at least two. -/
theorem matrix_nilpotent_kernel_dot_zero {n : ℕ}
    (N : Matrix (Fin n) (Fin n) F) (hN : IsNilpotent N)
    (hn : 2 ≤ n) (hrank : N.rank + 1 = n)
    (v u : Fin n → F) (hv : v ᵥ* N = 0) (hu : N *ᵥ u = 0) : v ⬝ᵥ u = 0 := by
  obtain ⟨w, hw⟩ := matrix_nilpotent_kernel_in_image N hN hn hrank u hu
  rw [← hw, Matrix.dotProduct_mulVec, hv, zero_dotProduct]

end DimensionFourDependence
