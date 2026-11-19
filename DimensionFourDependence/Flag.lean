import DimensionFourDependence.Nilpotent

/-! # Algebra of the nilpotent flag used in Lemma 2.2 -/

namespace DimensionFourDependence

open Matrix

variable {F : Type*} [Field F] {n r : ℕ}

/-- The reverse product in Sections 2.2 and 2.3 is nilpotent. -/
theorem nilpotent_reverse_product (A : Matrix (Fin n) (Fin r) F)
    (B : Matrix (Fin r) (Fin n) F) (h : IsNilpotent (A * B)) :
    IsNilpotent (B * A) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rw [mul_pow_succ_eq, hk, Matrix.mul_zero, Matrix.zero_mul]⟩

/-- The covector chain in Lemma 2.2 gives `aᵀM² = 0`. -/
theorem flag_second_annihilator (M : Matrix (Fin n) (Fin n) F)
    (a b : Fin n → F) (ha : a ᵥ* M = b) (hb : b ᵥ* M = 0) :
    a ᵥ* M ^ 2 = 0 := by
  rw [pow_two, ← vecMul_vecMul, ha, hb]

/-- The two gradients in Lemma 2.2 are independent: a relation between them
can be multiplied by `M` to isolate its first coefficient. -/
theorem flag_covectors_independent (M : Matrix (Fin n) (Fin n) F)
    (a b : Fin n → F) (hb0 : b ≠ 0) (ha : a ᵥ* M = b) (hb : b ᵥ* M = 0)
    (c d : F) (hrel : c • a + d • b = 0) : c = 0 ∧ d = 0 := by
  have h := congrArg (fun v => v ᵥ* M) hrel
  simp only [add_vecMul, smul_vecMul, ha, hb, smul_zero, add_zero, zero_vecMul] at h
  have hc : c = 0 := (smul_eq_zero.mp h).resolve_right hb0
  have hd : d = 0 := by
    rw [hc, zero_smul, zero_add] at hrel
    exact (smul_eq_zero.mp hrel).resolve_right hb0
  exact ⟨hc, hd⟩

/-- Both covectors kill the kernel direction when it is in `im M²`,
as it is for the single length-three Jordan block in Lemma 2.2. -/
theorem flag_kills_second_image (M : Matrix (Fin n) (Fin n) F)
    (a b z : Fin n → F) (ha : a ᵥ* M = b) (hb : b ᵥ* M = 0) :
    a ⬝ᵥ (M ^ 2 *ᵥ z) = 0 ∧ b ⬝ᵥ (M ^ 2 *ᵥ z) = 0 := by
  constructor
  · rw [dotProduct_mulVec, flag_second_annihilator M a b ha hb, zero_dotProduct]
  · rw [pow_two, ← mulVec_mulVec, dotProduct_mulVec, hb, zero_dotProduct]

end DimensionFourDependence
