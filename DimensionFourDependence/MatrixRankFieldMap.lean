import DimensionFourDependence.ScalarExtensionRank

/-! # Matrix ranks under field embeddings

A square matrix's invertible rank-normal-form factors remain invertible
under a field embedding. The diagonal normal form has the same support,
so its rank is unchanged. Full-row-rank right factors also preserve rank.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F E : Type*} [Field F] [Field E] {n m r : ℕ}

/-- A diagonal matrix keeps its rank under every field embedding. -/
theorem diagonal_rank_field_map (f : F →+* E) (w : Fin n → F) :
    ((diagonal w).map f).rank = (diagonal w).rank := by
  classical
  rw [diagonal_map (map_zero f), rank_diagonal, rank_diagonal]
  simp only [ne_eq, map_eq_zero_iff f f.injective]

/-- A square matrix keeps its actual rank after any field embedding. -/
theorem matrix_rank_field_map (f : F →+* E) (T : Matrix (Fin n) (Fin n) F) :
    (T.map f).rank = T.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, he⟩ := Matrix.exists_rank_normal_form T
  let D : Matrix (Fin n) (Fin n) F := (fromBlocks 1 0 0 0).submatrix e e
  have hVE : IsUnit (V.map f) := hV.map f.mapMatrix
  have hUE : IsUnit (U.map f) := hU.map f.mapMatrix
  have hVD : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det _).mp hV
  have hUD : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hVED : IsUnit (V.map f).det := (Matrix.isUnit_iff_isUnit_det _).mp hVE
  have hUED : IsUnit (U.map f).det := (Matrix.isUnit_iff_isUnit_det _).mp hUE
  have heE : V.map f * T.map f * U.map f = D.map f := by
    simpa only [Matrix.map_mul] using congrArg (fun M : Matrix (Fin n) (Fin n) F => M.map f) he
  have hD : (D.map f).rank = D.rank := by
    dsimp only [D]
    rw [← diagonal_one, ← diagonal_zero, fromBlocks_diagonal, submatrix_diagonal_equiv]
    exact diagonal_rank_field_map f _
  calc
    (T.map f).rank = (V.map f * T.map f * U.map f).rank := by
      rw [rank_mul_eq_left_of_isUnit_det _ _ hUED, rank_mul_eq_right_of_isUnit_det _ _ hVED]
    _ = (D.map f).rank := congrArg Matrix.rank heE
    _ = D.rank := hD
    _ = T.rank := by
      rw [show D = V * T * U from he.symm,
        rank_mul_eq_left_of_isUnit_det _ _ hUD, rank_mul_eq_right_of_isUnit_det _ _ hVD]

/-- Right multiplication by a full-row-rank matrix preserves rank. -/
theorem matrix_rank_mul_full_row_rank
    (A : Matrix (Fin m) (Fin r) F) (B : Matrix (Fin r) (Fin n) F) (hB : B.rank = r) :
    (A * B).rank = A.rank := by
  have htop : LinearMap.range B.toLin' = ⊤ := by
    apply Submodule.eq_top_iff_finrank_eq.mpr
    change B.rank = Module.finrank F (Fin r → F)
    simpa only [Module.finrank_pi, Fintype.card_fin] using hB
  have he : LinearMap.range (A * B).toLin' = LinearMap.range A.toLin' := by
    rw [Matrix.toLin'_mul, LinearMap.range_comp, htop, Submodule.map_top]
  exact congrArg (fun S : Submodule F (Fin m → F) => Module.finrank F S) he

end DimensionFourDependence
