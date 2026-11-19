import DimensionFourDependence.FiniteTrdegSelfEmbedding

/-! # Dominance forces a nonzero derivative along a preserved quadric ruling -/

namespace DimensionFourDependence

universe u
variable {K F : Type u} [Field K] [Field F] [CharZero K] [Algebra K F] [FinTrdeg K F]

set_option maxHeartbeats 3000000

/-- A dominant homogeneous quadric self-map preserving a ruling has
nonzero Wronskian along that ruling. The proof constructs a derivation
vanishing on the dominant image and contradicts its source coordinate values. -/
theorem dominant_quadric_ruling_wronskian_ne_zero
    (σ : F →ₐ[K] F) (Y : Fin 4 → F)
    (hgen : ∀ L : Derivation K F F, (∀ i, L (Y i) = 0) → ∀ z, L (σ z) = 0)
    (E D : Derivation K F F) (k x y t : F)
    (hk : k ≠ 0) (hx : x ≠ 0) (hY : Y 0 ≠ 0)
    (hweight : ∀ i, E (Y i) = k * Y i)
    (hEx : E x = x) (hEy : E y = y) (hDx : D x = 0) (hDy : D y = 1)
    (ht : D t = 0) (hpres : Y 2 = t * Y 0)
    (hquad : Y 0 * Y 3 = Y 1 * Y 2) :
    Y 0 * D (Y 1) - Y 1 * D (Y 0) ≠ 0 := by
  intro hzero
  let α := D (Y 0) / Y 0
  have h0 : D (Y 0) = α * Y 0 := by dsimp [α]; field_simp
  have h1 : D (Y 1) = α * Y 1 := by
    apply mul_left_cancel₀ hY
    rw [sub_eq_zero] at hzero
    rw [hzero, h0]
    ring
  have h2 : D (Y 2) = α * Y 2 := by
    rw [hpres, D.leibniz, ht, smul_zero, add_zero, smul_eq_mul, h0]
    ring
  have h3 : D (Y 3) = α * Y 3 := by
    have he := congrArg D hquad
    simp only [D.leibniz, smul_eq_mul, h0, h1, h2] at he
    apply mul_left_cancel₀ hY
    calc
      Y 0 * D (Y 3) = 2 * α * (Y 1 * Y 2) - α * (Y 0 * Y 3) := by linear_combination he
      _ = Y 0 * (α * Y 3) := by rw [← hquad]; ring
  let L : Derivation K F F := D - (α / k) • E
  have hL : L = 0 := derivation_zero_of_finite_trdeg_self_embedding σ L (hgen L (by
    intro i
    have hi : D (Y i) = α * Y i := by fin_cases i <;> assumption
    simp only [L, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul, hweight, hi]
    field_simp <;> ring))
  have hα : α / k = 0 := by
    have he := congrArg (fun A : Derivation K F F => A x) hL
    simp only [L, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul,
      hEx, hDx, Derivation.zero_apply, zero_sub, neg_eq_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hx
  have he := congrArg (fun A : Derivation K F F => A y) hL
  have hone : (1 : F) = 0 := by
    simpa only [L, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul,
      hEy, hDy, hα, zero_mul, sub_zero, Derivation.zero_apply] using he
  exact one_ne_zero hone

end DimensionFourDependence
