import DimensionFourDependence.RankTwoIsotropicPlane

/-! # Nonisotropic orthogonal directions for a rank-two form

A symmetric nonzero form in characteristic zero has a nonisotropic
vector. In dimension three, a rank-two form with a nonzero radial radical
has two orthogonal nonisotropic vectors transverse to that radical.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- A nonzero symmetric matrix cannot have identically zero quadratic form. -/
theorem symmetric_matrix_exists_nonisotropic
    (T : Matrix (Fin n) (Fin n) F) (hT : ∀ i j, T i j = T j i) (hT0 : T ≠ 0) :
    ∃ u : Fin n → F, matrixBilinearPairing T u u ≠ 0 := by
  by_contra hn
  have hzero : ∀ u : Fin n → F, matrixBilinearPairing T u u = 0 := by
    simpa only [not_exists, not_not] using hn
  have hB (u v : Fin n → F) : matrixBilinearPairing T u v = 0 := by
    have he := hzero (fun i => u i + v i)
    rw [matrixBilinearPairing_add_left, matrixBilinearPairing_add_right,
      matrixBilinearPairing_add_right, hzero, hzero,
      matrixBilinearPairing_symmetric T hT v u] at he
    have h2 : (2 : F) ≠ 0 := by norm_num
    apply (mul_eq_zero.mp (show 2 * matrixBilinearPairing T u v = 0 by linear_combination he)).resolve_left h2
  apply hT0
  ext i j
  change T i j = 0
  simpa only [matrixBilinearPairing, Pi.single_apply, mul_ite, ite_mul,
    mul_zero, zero_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
    hB (Pi.single i 1) (Pi.single j 1)

omit [CharZero F] in
/-- The plane spanned by a radical and an isotropic vector is totally
isotropic for the quadratic self-pairing. -/
theorem radical_isotropic_span_self_zero
    (T : Matrix (Fin n) (Fin n) F) (hT : ∀ i j, T i j = T j i)
    (Y Z : Fin n → F) (hY : ∀ v, matrixBilinearPairing T Y v = 0)
    (hZ : matrixBilinearPairing T Z Z = 0) (u : Fin n → F)
    (hu : u ∈ Submodule.span F (Set.range ![Y, Z])) : matrixBilinearPairing T u u = 0 := by
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (R := F)).mp hu
  have he : u = g 0 • Y + g 1 • Z := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hg.symm
  have hZY : matrixBilinearPairing T Z Y = 0 :=
    (matrixBilinearPairing_symmetric T hT Z Y).trans (hY Z)
  rw [he]
  change matrixBilinearPairing T (fun i => g 0 * Y i + g 1 * Z i)
    (fun i => g 0 * Y i + g 1 * Z i) = 0
  simp only [matrixBilinearPairing_add_left, matrixBilinearPairing_add_right,
    matrixBilinearPairing_scale_left, matrixBilinearPairing_scale_right,
    hY, hZY, hZ, mul_zero, add_zero]

/-- A rank-two symmetric form in dimension three has an orthogonal
nonisotropic pair, constructed using its nonzero radial radical. -/
theorem rank_two_exists_orthogonal_nonisotropic_pair
    (T : Matrix (Fin 3) (Fin 3) F) (hT : ∀ i j, T i j = T j i) (hrank : T.rank = 2)
    (Y : Fin 3 → F) (hY0 : Y ≠ 0) (hTY : T *ᵥ Y = 0) :
    ∃ u v : Fin 3 → F, matrixBilinearPairing T u u ≠ 0 ∧
      matrixBilinearPairing T v v ≠ 0 ∧ matrixBilinearPairing T u v = 0 := by
  classical
  have hY (w : Fin 3 → F) : matrixBilinearPairing T Y w = 0 := by
    rw [matrixBilinearPairing_symmetric T hT Y w, matrixBilinearPairing_eq_dot_mulVec,
      hTY, dotProduct_zero]
  have hT0 : T ≠ 0 := by
    intro he
    rw [he, Matrix.rank_zero] at hrank
    norm_num at hrank
  obtain ⟨u, hu⟩ := symmetric_matrix_exists_nonisotropic T hT hT0
  let S := Submodule.span F (Set.range ![Y, u])
  have hS : S ≠ ⊤ := by
    intro he
    have hb : finrank F S ≤ 2 := finrank_range_le_card (R := F) ![Y, u]
    rw [he] at hb
    simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at hb
    omega
  obtain ⟨w, hw⟩ := SetLike.exists_not_mem_of_ne_top S hS
  have hYS : Y ∈ S := Submodule.subset_span ⟨0, rfl⟩
  have huS : u ∈ S := Submodule.subset_span ⟨1, rfl⟩
  let r := matrixBilinearPairing T u w / matrixBilinearPairing T u u
  let v : Fin 3 → F := w + (-r) • u
  have huv : matrixBilinearPairing T u v = 0 := by
    change matrixBilinearPairing T u (fun i => w i + -r * u i) = 0
    rw [matrixBilinearPairing_add_right, matrixBilinearPairing_scale_right]
    dsimp only [r]
    field_simp [hu]
    ring
  have hvS : v ∉ S := by
    intro hv
    apply hw
    have he : w = v + r • u := by
      funext i
      change w i = (w i + -r * u i) + r * u i
      ring
    rw [he]
    exact S.add_mem hv (S.smul_mem r huS)
  have hvY : LinearIndependent F ![v, Y] := by
    apply linearIndependent_fin2.mpr
    refine ⟨hY0, ?_⟩
    intro a he
    change a • Y = v at he
    apply hvS
    rw [← he]
    exact S.smul_mem a hYS
  have hYv : LinearIndependent F ![Y, v] := by
    have he : (fun i : Fin 2 => ![v, Y] ((Equiv.swap 0 1) i)) = ![Y, v] := by
      funext i
      fin_cases i <;> rfl
    rw [← he]
    exact hvY.comp (Equiv.swap 0 1) (Equiv.swap 0 1).injective
  refine ⟨u, v, hu, ?_, huv⟩
  intro hv
  have hmem := rank_two_isotropic_orthogonal_plane T hT hrank Y v hYv hTY hv u huv
  exact hu (radical_isotropic_span_self_zero T hT Y v hY hv u hmem)

end DimensionFourDependence
