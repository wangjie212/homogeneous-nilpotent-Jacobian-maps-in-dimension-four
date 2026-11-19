import DimensionFourDependence.NilpotentFlag

/-! # The third step of the nilpotent flag for the cubic invariant -/

namespace DimensionFourDependence

open Matrix

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- A one-dimensional kernel can grow to dimension at most two on squaring. -/
theorem finrank_ker_square_le_two (f : Module.End F V)
    (hdim : Module.finrank F (LinearMap.ker f) = 1) :
    Module.finrank F (LinearMap.ker (f ^ 2)) ≤ 2 := by
  have hr : Module.rank F (LinearMap.ker f) = 1 :=
    Module.rank_eq_one_iff_finrank_eq_one.mpr hdim
  have hb := f.lift_rank_comap_le (LinearMap.ker f)
  have hbound : Module.rank F (LinearMap.ker (f ^ 2)) ≤ (2 : Cardinal) := by
    rw [pow_two, Module.End.mul_eq_comp, LinearMap.ker_comp]
    simpa only [Cardinal.lift_id, hr, one_add_one_eq_two] using hb
  exact Module.finrank_le_of_rank_le hbound

/-- Rank three in dimension four forces a nonzero third power, even
without nilpotence. -/
theorem rank_three_matrix_cube_ne_zero (N : Matrix (Fin 4) (Fin 4) F)
    (hrank : N.rank = 3) : N ^ 3 ≠ 0 := by
  have hd := LinearMap.finrank_range_add_finrank_ker N.toLin'
  have hr : Module.finrank F (LinearMap.range N.toLin') = 3 := hrank
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  have hk : Module.finrank F (LinearMap.ker N.toLin') = 1 := by omega
  have hk2 := finrank_ker_square_le_two N.toLin' hk
  have hd2 := LinearMap.finrank_range_add_finrank_ker (N.toLin' ^ 2)
  rw [← Matrix.toLin'_pow] at hk2 hd2
  have hr2 : Module.finrank F (LinearMap.range (N ^ 2).toLin') = (N ^ 2).rank := rfl
  simp only [Module.finrank_pi, Fintype.card_fin] at hd2
  intro h
  have hb := Matrix.rank_add_rank_le_card_of_mul_eq_zero
    (A := N) (B := N ^ 2) (by simpa only [pow_succ'] using h)
  simp only [Fintype.card_fin, hrank] at hb
  omega

/-- The third image contains the kernel direction of a nilpotent
rank-three matrix in dimension four. -/
theorem matrix_nilpotent_kernel_in_cube_image
    (N : Matrix (Fin 4) (Fin 4) F) (hN : IsNilpotent N) (hrank : N.rank = 3)
    (u : Fin 4 → F) (hu : N *ᵥ u = 0) : ∃ w, N ^ 3 *ᵥ w = u := by
  have hN3 := rank_three_matrix_cube_ne_zero N hrank
  have hnil : IsNilpotent N.toLin' := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by rw [← Matrix.toLin'_pow, hk]; simp⟩
  have hp : N.toLin' ^ 3 ≠ 0 := by
    intro h
    apply hN3
    apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_pow, map_zero] using h
  have hd := LinearMap.finrank_range_add_finrank_ker N.toLin'
  have hr : Module.finrank F (LinearMap.range N.toLin') = 3 := hrank
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  have hk : Module.finrank F (LinearMap.ker N.toLin') = 1 := by omega
  obtain ⟨w, hw⟩ := nilpotent_kernel_le_power_range N.toLin' hnil 3 hp hk hu
  refine ⟨w, ?_⟩
  rw [← Matrix.toLin'_pow] at hw
  exact hw

/-- The third covector of a nilpotent chain annihilates the kernel. -/
theorem nilpotent_third_covector_kernel_dot_zero
    (N : Matrix (Fin 4) (Fin 4) F) (hN : IsNilpotent N) (hrank : N.rank = 3)
    (a b c u : Fin 4 → F) (ha : a ᵥ* N = b) (hb : b ᵥ* N = c)
    (hc : c ᵥ* N = 0) (hu : N *ᵥ u = 0) : a ⬝ᵥ u = 0 := by
  obtain ⟨w, hw⟩ := matrix_nilpotent_kernel_in_cube_image N hN hrank u hu
  have hz : a ᵥ* N ^ 3 = 0 := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, pow_two,
      ← vecMul_vecMul, ← vecMul_vecMul, ha, hb, hc]
  rw [← hw, dotProduct_mulVec, hz, zero_dotProduct]

/-- The two upper covectors of a three-step chain are independent when
the bottom covector is nonzero. -/
theorem three_step_covectors_independent {n : ℕ}
    (N : Matrix (Fin n) (Fin n) F) (a b c : Fin n → F)
    (hc0 : c ≠ 0) (ha : a ᵥ* N = b) (hb : b ᵥ* N = c) (hc : c ᵥ* N = 0)
    (s t : F) (hrel : s • a + t • b = 0) : s = 0 ∧ t = 0 := by
  have h := congrArg (fun v => v ᵥ* N) hrel
  simp only [add_vecMul, smul_vecMul, ha, hb, zero_vecMul] at h
  exact flag_covectors_independent N b c hc0 hb hc s t h

end DimensionFourDependence
