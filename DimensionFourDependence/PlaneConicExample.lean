import DimensionFourDependence.Nilpotent
import DimensionFourDependence.Homogeneous

/-! # The homogeneous conic example of Section 5.6 -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4500000

variable {K : Type u} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K

noncomputable def planeConicExampleQuadratic : R₄ := X 1 * X 3 - X 0 ^ 2

/-- The displayed example, indexed by its total homogeneous degree. -/
noncomputable def planeConicExample (d : ℕ) : Fin 4 → R₄ :=
  let Q := planeConicExampleQuadratic (K := K)
  let w := (X 3 : R₄)
  fun i => w ^ (d - 4) * (![w ^ 2 * Q, w ^ 3 * X 2 + 2 * X 0 * w * Q, -Q ^ 2, 0] : Fin 4 → R₄) i

theorem planeConicExample_last (d : ℕ) : planeConicExample (K := K) d (Fin.last 3) = 0 := by
  change (X 3 : R₄) ^ (d - 4) * 0 = 0
  rw [mul_zero]

theorem planeConicExample_homogeneous {d : ℕ} (hd : 4 ≤ d) :
    IsHomogMap (planeConicExample (K := K) d) d := by
  have hx (i : Fin 4) : (X i : R₄).IsHomogeneous 1 := by
    simpa only [pow_one] using isHomogeneous_X_pow (R := K) i 1
  have hQ : (planeConicExampleQuadratic (K := K)).IsHomogeneous 2 :=
    (hx 1 |>.mul (hx 3)).sub (isHomogeneous_X_pow (R := K) 0 2)
  have h₂ : ((X 3 : R₄) ^ 2 * planeConicExampleQuadratic).IsHomogeneous 4 :=
    (isHomogeneous_X_pow (R := K) 3 2).mul hQ
  have h₃ : ((X 3 : R₄) ^ 3 * X 2 + 2 * X 0 * X 3 * planeConicExampleQuadratic).IsHomogeneous 4 := by
    apply ((isHomogeneous_X_pow (R := K) 3 3).mul (hx 2)).add
    have h := ((hx 0).C_mul (2 : K)).mul (hx 3) |>.mul hQ
    simpa only [map_ofNat] using h
  have h₄ : (-(planeConicExampleQuadratic (K := K)) ^ 2).IsHomogeneous 4 := (hQ.pow 2).neg
  have hw := isHomogeneous_X_pow (R := K) (σ := Fin 4) 3 (d - 4)
  have hdegree : d - 4 + 4 = d := by omega
  intro i
  refine hdegree ▸ ?_
  apply hw.mul
  fin_cases i
  · exact h₂
  · exact h₃
  · exact h₄
  · exact isHomogeneous_zero _ _ _

private def conicJacobianBlock {R : Type*} [CommRing R] (x w q : R) : Matrix (Fin 3) (Fin 3) R :=
  of ![![-2 * x * w ^ 2, w ^ 3, 0],
    ![2 * w * q - 4 * x ^ 2 * w, 2 * x * w ^ 2, w ^ 3],
    ![4 * x * q, -2 * w * q, 0]]

private theorem conicJacobianBlock_cube_zero {R : Type*} [CommRing R] (x w q : R) :
    conicJacobianBlock x w q ^ 3 = 0 := by
  funext i j
  rw [pow_succ, pow_two]
  fin_cases i <;> fin_cases j <;>
    simp [conicJacobianBlock, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem planeConicExample_jacobian_block (d : ℕ) :
    (jac (planeConicExample (K := K) d)).submatrix Fin.castSucc Fin.castSucc =
      (X 3 : R₄) ^ (d - 4) • conicJacobianBlock (X 0) (X 3) planeConicExampleQuadratic := by
  funext i j
  change pderiv j.castSucc (planeConicExample d i.castSucc) = _
  have htwo (j : Fin 4) : pderiv j (2 : R₄) = 0 := by
    rw [← map_ofNat (C : K →+* R₄), pderiv_C]
  fin_cases i <;> fin_cases j <;>
    simp [planeConicExample, conicJacobianBlock, planeConicExampleQuadratic,
      Derivation.leibniz, smul_eq_mul, htwo] <;> ring

private theorem zero_last_row_power_submatrix {R : Type*} [CommRing R] {n : ℕ}
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hN : ∀ j, N (Fin.last n) j = 0) (k : ℕ) :
    (N ^ k).submatrix Fin.castSucc Fin.castSucc = (N.submatrix Fin.castSucc Fin.castSucc) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    funext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, Fin.castSucc_inj]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    funext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [Fin.sum_univ_castSucc, hN, mul_zero, add_zero]
    exact Finset.sum_congr rfl (fun t _ => congrArg (fun a => a * N t.castSucc j.castSucc)
      (congrFun (congrFun ih i) t))

theorem planeConicExample_nilpotent (d : ℕ) : IsNilpotent (jac (planeConicExample (K := K) d)) := by
  let N := jac (planeConicExample (K := K) d)
  have hrow (j : Fin 4) : N (Fin.last 3) j = 0 := by
    change pderiv j (planeConicExample (K := K) d (Fin.last 3)) = 0
    rw [planeConicExample_last, map_zero]
  have hblock : (N ^ 3).submatrix Fin.castSucc Fin.castSucc = 0 := by
    rw [zero_last_row_power_submatrix N hrow, planeConicExample_jacobian_block, smul_pow,
      conicJacobianBlock_cube_zero, smul_zero]
  refine ⟨4, ?_⟩
  change N ^ 4 = 0
  have hpowrow (k : ℕ) (j : Fin 4) : (N ^ (k + 1)) (Fin.last 3) j = 0 := by
    rw [pow_succ', Matrix.mul_apply]
    simp only [hrow, zero_mul, Finset.sum_const_zero]
  funext i j
  refine Fin.lastCases (hpowrow 3 j) (fun i => ?_) i
  change (N ^ (3 + 1 : ℕ)) i.castSucc j = 0
  rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_castSucc, hrow, mul_zero, add_zero]
  apply Finset.sum_eq_zero
  intro t _
  have ht : (N ^ 3) i.castSucc t.castSucc = 0 := congrFun (congrFun hblock i) t
  rw [ht, zero_mul]

private theorem planeConicExample_rank_minor_at_point (m : ℕ) :
    let p : Fin 4 → K := ![0, 1, 0, 1]
    let N := (jac (planeConicExample (K := K) (m + 4))).submatrix Fin.castSucc (Fin.succ : Fin 3 → Fin 4)
    aeval p N.det = (m : K) + 4 := by
  let p : Fin 4 → K := ![0, 1, 0, 1]
  let N := (jac (planeConicExample (K := K) (m + 4))).submatrix Fin.castSucc (Fin.succ : Fin 3 → Fin 4)
  have he : N.map (aeval p) = of ![![1, 0, (m : K) + 3], ![0, 1, 0], ![-2, 0, -((m : K) + 2)]] := by
    funext i j
    change aeval p (pderiv (Fin.succ j) (planeConicExample (K := K) (m + 4) i.castSucc)) = _
    fin_cases i <;> fin_cases j <;>
      simp [planeConicExample, planeConicExampleQuadratic, Derivation.leibniz, p, smul_eq_mul] <;> ring
  calc
    aeval p N.det = (N.map (aeval p)).det := RingHom.map_det (aeval p).toRingHom N
    _ = (m : K) + 4 := by
      rw [he, Matrix.det_fin_three]
      simp
      ring

/-- The homogeneous example is nilpotent of rank three with zero final output. -/
theorem plane_conic_example_homogeneous_nilpotent_rank_three [CharZero K] {d : ℕ} (hd : 4 ≤ d) :
    let H := planeConicExample (K := K) d
    IsHomogMap H d ∧ IsNilpotent (jac H) ∧ polyRank (jac H) = 3 ∧ H (Fin.last 3) = 0 := by
  let H := planeConicExample (K := K) d
  have hN := planeConicExample_nilpotent (K := K) d
  let N := (jac H).submatrix Fin.castSucc (Fin.succ : Fin 3 → Fin 4)
  have hminor : N.det ≠ 0 := by
    intro h
    have he := planeConicExample_rank_minor_at_point (K := K) (d - 4)
    rw [Nat.sub_add_cancel hd] at he
    change aeval (![0, 1, 0, 1] : Fin 4 → K) N.det = ((d - 4 : ℕ) : K) + 4 at he
    rw [h, map_zero, ← Nat.cast_ofNat (R := K) (n := 4), ← Nat.cast_add, Nat.sub_add_cancel hd] at he
    exact (Nat.cast_ne_zero.mpr (by omega : d ≠ 0)) he.symm
  let f := algebraMap R₄ (FractionRing R₄)
  have hdN : (N.map f).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hminor (IsFractionRing.injective R₄ (FractionRing R₄) (h.trans (map_zero f).symm))
  have hle := Matrix.rank_submatrix_le ((jac H).map f) Fin.castSucc (Fin.succ : Fin 3 → Fin 4)
  change (N.map f).rank ≤ polyRank (jac H) at hle
  rw [Matrix.rank_of_det_ne_zero hdN, Fintype.card_fin] at hle
  exact ⟨planeConicExample_homogeneous hd, hN, le_antisymm (rank_at_most_three H hN) hle, planeConicExample_last d⟩

end DimensionFourDependence
