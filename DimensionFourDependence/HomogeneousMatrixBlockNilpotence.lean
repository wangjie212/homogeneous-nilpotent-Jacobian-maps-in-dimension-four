import DimensionFourDependence.LastCoordinateDehomogenization

/-! # Recovering nilpotence of a homogeneous block matrix from its final-coordinate chart -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 2200000

variable {R : Type*} [CommRing R] {n : ℕ}

theorem leading_block_pow_of_last_row_zero
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hz : ∀ j, M (Fin.last n) j = 0) (k : ℕ) :
    (M ^ k).submatrix Fin.castSucc Fin.castSucc = (M.submatrix Fin.castSucc Fin.castSucc) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    ext i j
    simp [Matrix.one_apply, Fin.castSucc_inj]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    funext i j
    change (∑ l : Fin (n + 1), (M ^ k) i.castSucc l * M l j.castSucc) =
      ∑ l : Fin n, ((M.submatrix Fin.castSucc Fin.castSucc) ^ k) i l * M l.castSucc j.castSucc
    rw [Fin.sum_univ_castSucc]
    simp only [hz, mul_zero, add_zero]
    rw [← ih]
    rfl

theorem block_pow_succ_zero_of_leading_block_pow_zero
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hz : ∀ j, M (Fin.last n) j = 0)
    {k : ℕ} (hk : 0 < k) (hn : (M.submatrix Fin.castSucc Fin.castSucc) ^ k = 0) : M ^ (k + 1) = 0 := by
  have hlead := (leading_block_pow_of_last_row_zero M hz k).trans hn
  have hlast (j : Fin (n + 1)) : (M ^ k) (Fin.last n) j = 0 := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [pow_succ']
    simp [Matrix.mul_apply, hz]
  have hcol (i : Fin (n + 1)) (j : Fin n) : (M ^ k) i j.castSucc = 0 := by
    refine Fin.lastCases (hlast _) (fun i => ?_) i
    exact congrFun (congrFun hlead i) j
  rw [pow_succ]
  funext i j
  change (∑ l : Fin (n + 1), (M ^ k) i l * M l j) = 0
  rw [Fin.sum_univ_castSucc]
  simp [hcol, hz]

variable {K σ ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem homogeneous_matrix_power_entries
    (M : Matrix ι ι (MvPolynomial σ K)) {m : ℕ}
    (hM : ∀ i j, (M i j).IsHomogeneous m) (k : ℕ) :
    ∀ i j, ((M ^ k) i j).IsHomogeneous (k * m) := by
  classical
  induction k with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply, zero_mul]
    by_cases h : i = j <;> simp [h, isHomogeneous_one, isHomogeneous_zero]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply, Nat.succ_mul]
    exact IsHomogeneous.sum _ _ _ (fun l _ => (ih i l).mul (hM l j))

/-- A homogeneous matrix power vanishes if its exact dehomogenization
vanishes. The common entry degree makes the chart injective on the power. -/
theorem homogeneous_matrix_pow_zero_of_dehomogenize_pow_zero
    (M : Matrix ι ι (MvPolynomial (Fin (n + 1)) K)) {m k : ℕ}
    (hh : ∀ i j, (M i j).IsHomogeneous m)
    (hz : M.map (lastCoordinateDehomogenize (K := K) (n := n)) ^ k = 0) : M ^ k = 0 := by
  have he : (M ^ k).map (lastCoordinateDehomogenize (K := K) (n := n)) = 0 := by
    exact ((lastCoordinateDehomogenize (K := K) (n := n)).toRingHom.mapMatrix.map_pow M k).trans hz
  funext i j
  apply lastCoordinateDehomogenize_injective_on_homogeneous_degree _ _
    (homogeneous_matrix_power_entries M hh k i j) (isHomogeneous_zero _ _ _)
  change lastCoordinateDehomogenize ((M ^ k) i j) = lastCoordinateDehomogenize 0
  rw [map_zero]
  exact congrFun (congrFun he i) j

end DimensionFourDependence
