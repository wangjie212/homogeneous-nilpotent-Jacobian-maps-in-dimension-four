import DimensionFourDependence.NilpotentKernel

/-! # Higher steps of the nilpotent flag in Lemma 2.2 -/

namespace DimensionFourDependence

open Matrix

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- A nonzero power of a nilpotent operator has a nonzero image vector
annihilated by the original operator. -/
theorem nilpotent_nonzero_power_kernel_image (f : Module.End F V)
    (hf : IsNilpotent f) (r : ℕ) (hr : f ^ r ≠ 0) :
    ∃ w : V, (f ^ r) w ≠ 0 ∧ f ((f ^ r) w) = 0 := by
  classical
  obtain ⟨m, hm⟩ := hf
  have hex : ∃ k : ℕ, f ^ (k + r + 1) = 0 :=
    ⟨m, by rw [show m + r + 1 = m + (r + 1) by omega, pow_add, hm, zero_mul]⟩
  let k := Nat.find hex
  have hk : f ^ (k + r + 1) = 0 := Nat.find_spec hex
  have hprev : f ^ (k + r) ≠ 0 := by
    intro h
    cases he : k with
    | zero => exact hr (by simpa [he] using h)
    | succ t =>
      have ht : t < Nat.find hex := by omega
      exact Nat.find_min hex ht (by simpa only [he, Nat.succ_eq_add_one,
        show t + 1 + r = t + r + 1 by omega] using h)
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hprev
  refine ⟨(f ^ k) v, ?_, ?_⟩
  · rw [show k + r = r + k by omega, pow_add] at hv
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using hv
  · have h := congrArg (fun g : Module.End F V => g v) hk
    rw [pow_succ', show k + r = r + k by omega, pow_add] at h
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using h

/-- In corank one, the kernel is contained in the image of every nonzero
power of a nilpotent operator. -/
theorem nilpotent_kernel_le_power_range [FiniteDimensional F V]
    (f : Module.End F V) (hf : IsNilpotent f) (r : ℕ) (hr : f ^ r ≠ 0)
    (hdim : Module.finrank F (LinearMap.ker f) = 1) :
    LinearMap.ker f ≤ LinearMap.range (f ^ r) := by
  obtain ⟨w, hw0, hw⟩ := nilpotent_nonzero_power_kernel_image f hf r hr
  let z : LinearMap.ker f := ⟨(f ^ r) w, hw⟩
  have hz : z ≠ 0 := by
    intro h
    exact hw0 (congrArg Subtype.val h)
  intro u hu
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' z hz).mp hdim ⟨u, hu⟩
  refine ⟨c • w, ?_⟩
  have he := congrArg Subtype.val hc
  simpa only [map_smul, Submodule.coe_smul_of_tower] using he

/-- The second image contains the kernel of a nilpotent rank-three
four-by-four matrix. -/
theorem matrix_nilpotent_kernel_in_square_image
    (N : Matrix (Fin 4) (Fin 4) F) (hN : IsNilpotent N) (hrank : N.rank = 3)
    (u : Fin 4 → F) (hu : N *ᵥ u = 0) : ∃ w, N ^ 2 *ᵥ w = u := by
  have hN2 : N ^ 2 ≠ 0 := by
    intro h
    have hb := Matrix.rank_add_rank_le_card_of_mul_eq_zero
      (A := N) (B := N) (by simpa only [pow_two] using h)
    simp only [Fintype.card_fin, hrank] at hb
    omega
  have hnil : IsNilpotent N.toLin' := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by rw [← Matrix.toLin'_pow, hk]; simp⟩
  have hp : N.toLin' ^ 2 ≠ 0 := by
    intro h
    apply hN2
    apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_pow, map_zero] using h
  have hd := LinearMap.finrank_range_add_finrank_ker N.toLin'
  have hr : Module.finrank F (LinearMap.range N.toLin') = 3 := hrank
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  have hk : Module.finrank F (LinearMap.ker N.toLin') = 1 := by omega
  obtain ⟨w, hw⟩ := nilpotent_kernel_le_power_range N.toLin' hnil 2 hp hk hu
  refine ⟨w, ?_⟩
  rw [← Matrix.toLin'_pow] at hw
  exact hw

/-- The second covector in a nilpotent chain kills the kernel direction. -/
theorem nilpotent_second_covector_kernel_dot_zero
    (N : Matrix (Fin 4) (Fin 4) F) (hN : IsNilpotent N) (hrank : N.rank = 3)
    (a b u : Fin 4 → F) (ha : a ᵥ* N = b) (hb : b ᵥ* N = 0)
    (hu : N *ᵥ u = 0) : a ⬝ᵥ u = 0 := by
  obtain ⟨w, hw⟩ := matrix_nilpotent_kernel_in_square_image N hN hrank u hu
  rw [← hw, dotProduct_mulVec, flag_second_annihilator N a b ha hb, zero_dotProduct]

end DimensionFourDependence
