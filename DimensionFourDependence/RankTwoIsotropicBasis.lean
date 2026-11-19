import DimensionFourDependence.RankTwoOrthogonalPair

/-! # Constructing the two isotropic directions modulo the radial radical

Over algebraically closed constants, the orthogonal nonisotropic pair
splits into two isotropic vectors with nonzero mixed pairing. Together
with the nonzero radial radical these vectors form a basis.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
/-- An isotropic pair with nonzero mixed pairing is independent modulo
any nonzero radical vector. -/
theorem radical_isotropic_triple_independent
    (T : Matrix (Fin n) (Fin n) F) (hT : ∀ i j, T i j = T j i)
    (Y Z W : Fin n → F) (hY0 : Y ≠ 0)
    (hY : ∀ v, matrixBilinearPairing T Y v = 0)
    (hZ : matrixBilinearPairing T Z Z = 0) (hW : matrixBilinearPairing T W W = 0)
    (hκ : matrixBilinearPairing T Z W ≠ 0) : LinearIndependent F ![Y, Z, W] := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  have he : g 0 • Y + g 1 • Z + g 2 • W = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hg
  have hZY : matrixBilinearPairing T Z Y = 0 :=
    (matrixBilinearPairing_symmetric T hT Z Y).trans (hY Z)
  have hWY : matrixBilinearPairing T W Y = 0 :=
    (matrixBilinearPairing_symmetric T hT W Y).trans (hY W)
  have hWZ : matrixBilinearPairing T W Z = matrixBilinearPairing T Z W :=
    matrixBilinearPairing_symmetric T hT W Z
  have hzero (v : Fin n → F) : matrixBilinearPairing T v 0 = 0 := by
    simp only [matrixBilinearPairing, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have heZ := congrArg (fun v => matrixBilinearPairing T Z v) he
  change matrixBilinearPairing T Z (fun j => g 0 * Y j + g 1 * Z j + g 2 * W j) = _ at heZ
  simp only [matrixBilinearPairing_add_right, matrixBilinearPairing_scale_right,
    hZY, hZ, hzero, mul_zero, zero_add] at heZ
  have hg2 : g 2 = 0 := (mul_eq_zero.mp heZ).resolve_right hκ
  have heW := congrArg (fun v => matrixBilinearPairing T W v) he
  change matrixBilinearPairing T W (fun j => g 0 * Y j + g 1 * Z j + g 2 * W j) = _ at heW
  simp only [matrixBilinearPairing_add_right, matrixBilinearPairing_scale_right,
    hWY, hW, hWZ, hzero, mul_zero, zero_add, add_zero] at heW
  have hg1 : g 1 = 0 := (mul_eq_zero.mp heW).resolve_right hκ
  simp only [hg1, hg2, zero_smul, add_zero] at he
  have hg0 : g 0 = 0 := (smul_eq_zero.mp he).resolve_right hY0
  fin_cases i <;> assumption

variable [IsAlgClosed F]

/-- An orthogonal nonisotropic pair splits into an isotropic pair
with nonzero mixed pairing over algebraically closed constants. -/
theorem orthogonal_nonisotropic_pair_splits
    (T : Matrix (Fin n) (Fin n) F) (hT : ∀ i j, T i j = T j i)
    (u v : Fin n → F) (hu : matrixBilinearPairing T u u ≠ 0)
    (hv : matrixBilinearPairing T v v ≠ 0) (huv : matrixBilinearPairing T u v = 0) :
    ∃ Z W : Fin n → F, matrixBilinearPairing T Z Z = 0 ∧
      matrixBilinearPairing T W W = 0 ∧ matrixBilinearPairing T Z W ≠ 0 := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self (-matrixBilinearPairing T v v / matrixBilinearPairing T u u)
  have hrq : r * r * matrixBilinearPairing T u u = -matrixBilinearPairing T v v := by
    rw [← hr, div_mul_cancel₀ _ hu]
  have hvu : matrixBilinearPairing T v u = 0 :=
    (matrixBilinearPairing_symmetric T hT v u).trans huv
  let Z : Fin n → F := fun i => v i + r * u i
  let W : Fin n → F := fun i => v i + -r * u i
  have hZ : matrixBilinearPairing T Z Z = 0 := by
    dsimp only [Z]
    simp only [matrixBilinearPairing_add_left, matrixBilinearPairing_add_right,
      matrixBilinearPairing_scale_left, matrixBilinearPairing_scale_right,
      huv, hvu, mul_zero, zero_add, add_zero]
    linear_combination hrq
  have hW : matrixBilinearPairing T W W = 0 := by
    dsimp only [W]
    simp only [matrixBilinearPairing_add_left, matrixBilinearPairing_add_right,
      matrixBilinearPairing_scale_left, matrixBilinearPairing_scale_right,
      huv, hvu, mul_zero, zero_add, add_zero]
    linear_combination hrq
  have hZW : matrixBilinearPairing T Z W = 2 * matrixBilinearPairing T v v := by
    dsimp only [Z, W]
    simp only [matrixBilinearPairing_add_left, matrixBilinearPairing_add_right,
      matrixBilinearPairing_scale_left, matrixBilinearPairing_scale_right,
      huv, hvu, mul_zero, zero_add, add_zero]
    linear_combination -hrq
  refine ⟨Z, W, hZ, hW, ?_⟩
  rw [hZW]
  exact mul_ne_zero (by norm_num) hv

/-- A symmetric rank-two form with nonzero radial radical has two
isotropic vectors with nonzero mixed pairing over algebraically closed constants. -/
theorem rank_two_exists_isotropic_pair
    (T : Matrix (Fin 3) (Fin 3) F) (hT : ∀ i j, T i j = T j i) (hrank : T.rank = 2)
    (Y : Fin 3 → F) (hY0 : Y ≠ 0) (hTY : T *ᵥ Y = 0) :
    ∃ Z W : Fin 3 → F, matrixBilinearPairing T Z Z = 0 ∧
      matrixBilinearPairing T W W = 0 ∧ matrixBilinearPairing T Z W ≠ 0 := by
  obtain ⟨u, v, hu, hv, huv⟩ := rank_two_exists_orthogonal_nonisotropic_pair T hT hrank Y hY0 hTY
  exact orthogonal_nonisotropic_pair_splits T hT u v hu hv huv

/-- The two isotropic directions are constructed and form a basis
together with the radial radical; this is the coordinate choice in Section 3.2. -/
theorem rank_two_exists_radial_isotropic_basis
    (T : Matrix (Fin 3) (Fin 3) F) (hT : ∀ i j, T i j = T j i) (hrank : T.rank = 2)
    (Y : Fin 3 → F) (hY0 : Y ≠ 0) (hTY : T *ᵥ Y = 0) :
    ∃ Z W : Fin 3 → F, matrixBilinearPairing T Z Z = 0 ∧
      matrixBilinearPairing T W W = 0 ∧ matrixBilinearPairing T Z W ≠ 0 ∧
      LinearIndependent F ![Y, Z, W] ∧
      Submodule.span F (Set.range ![Y, Z, W]) = ⊤ := by
  obtain ⟨Z, W, hZ, hW, hκ⟩ := rank_two_exists_isotropic_pair T hT hrank Y hY0 hTY
  have hY (v : Fin 3 → F) : matrixBilinearPairing T Y v = 0 := by
    rw [matrixBilinearPairing_symmetric T hT Y v, matrixBilinearPairing_eq_dot_mulVec,
      hTY, dotProduct_zero]
  have hli := radical_isotropic_triple_independent T hT Y Z W hY0 hY hZ hW hκ
  refine ⟨Z, W, hZ, hW, hκ, hli, ?_⟩
  apply Submodule.eq_top_iff_finrank_eq.mpr
  simpa only [Module.finrank_pi, Fintype.card_fin] using finrank_span_eq_card hli

end DimensionFourDependence
