import DimensionFourDependence.NilpotentFlag

/-! # The first three vectors of a nontrivial nilpotent orbit are independent -/

namespace DimensionFourDependence

open Matrix

set_option maxHeartbeats 2500000

variable {F : Type*} [Field F] {n : ℕ}

/-- A nonzero second iterate of a nilpotent matrix constructs an
independent three-vector orbit. The proof uses the actual last nonzero
iterate of this vector, without assuming a Jordan normal form. -/
theorem nilpotent_second_iterate_ne_zero_three_vector_orbit_independent
    (N : Matrix (Fin n) (Fin n) F) (hN : IsNilpotent N)
    (x : Fin n → F) (hx : N ^ 2 *ᵥ x ≠ 0) :
    LinearIndependent F ![x, N *ᵥ x, N ^ 2 *ᵥ x] := by
  classical
  let w : ℕ → (Fin n → F) := fun r => N ^ r *ᵥ x
  have hwadd (r s : ℕ) : N ^ r *ᵥ w s = w (r + s) := by
    change N ^ r *ᵥ (N ^ s *ᵥ x) = N ^ (r + s) *ᵥ x
    rw [Matrix.mulVec_mulVec, ← pow_add]
  obtain ⟨m, hm⟩ := hN
  have hex : ∃ k : ℕ, w (k + 3) = 0 := by
    refine ⟨m, ?_⟩
    simp [w, pow_add, hm]
  let k := Nat.find hex
  have hk : w (k + 3) = 0 := Nat.find_spec hex
  have hprev : w (k + 2) ≠ 0 := by
    intro hz
    cases he : k with
    | zero => exact hx (by simpa only [he, zero_add] using hz)
    | succ j =>
      exact Nat.find_min hex (by change j < k; omega)
        (by simpa only [he, Nat.succ_eq_add_one, Nat.add_assoc] using hz)
  have hnext : w (k + 4) = 0 := by
    have he := congrArg (fun z => N ^ 1 *ᵥ z) hk
    rw [hwadd, Matrix.mulVec_zero] at he
    simpa only [show 1 + (k + 3) = k + 4 by omega] using he
  have hli : LinearIndependent F ![w 0, w 1, w 2] := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have hrel : a 0 • w 0 + a 1 • w 1 + a 2 • w 2 = 0 := by
      simpa [Fin.sum_univ_succ, add_assoc] using ha
    have h0 : a 0 = 0 := by
      have he := congrArg (fun z => N ^ (k + 2) *ᵥ z) hrel
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hwadd,
        Matrix.mulVec_zero] at he
      have hs : a 0 • w (k + 2) = 0 := by
        simpa only [Nat.add_zero, Nat.add_assoc, hk, hnext, smul_zero, add_zero] using he
      exact (smul_eq_zero.mp hs).resolve_right hprev
    have h1 : a 1 = 0 := by
      have he := congrArg (fun z => N ^ (k + 1) *ᵥ z) hrel
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hwadd,
        Matrix.mulVec_zero] at he
      have hs : a 1 • w (k + 2) = 0 := by
        simpa only [h0, zero_smul, zero_add, Nat.add_assoc, hk, smul_zero, add_zero] using he
      exact (smul_eq_zero.mp hs).resolve_right hprev
    have h2 : a 2 = 0 := by
      have he := congrArg (fun z => N ^ k *ᵥ z) hrel
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hwadd,
        Matrix.mulVec_zero, h0, h1, zero_smul, zero_add] at he
      exact (smul_eq_zero.mp he).resolve_right hprev
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  simpa only [w, pow_zero, pow_one, Matrix.one_mulVec] using hli

end DimensionFourDependence
