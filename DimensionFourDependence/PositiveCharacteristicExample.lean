import DimensionFourDependence.Nilpotent
import DimensionFourDependence.Homogeneous

/-! # The positive-characteristic counterexample in Section 5.6 -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4300000

variable {K : Type u} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K

/-- The original perturbation over a field of positive characteristic. -/
noncomputable def positiveCharacteristicExample (p : ℕ) : Fin 4 → R₄ :=
  let a := (X 0 : R₄) ^ p
  let b := (X 1 : R₄) ^ p
  ![a * X 1, a * X 2, a * X 3 - b * X 0, b * X 1]

theorem positiveCharacteristicExample_jacobian (p : ℕ) [CharP K p] :
    let a := (X 0 : R₄) ^ p
    let b := (X 1 : R₄) ^ p
    jac (positiveCharacteristicExample p) = Matrix.of ![![0, a, 0, 0], ![0, 0, a, 0], ![-b, 0, 0, a], ![0, b, 0, 0]] := by
  funext i j
  change pderiv j (positiveCharacteristicExample p i) = _
  fin_cases i <;> fin_cases j <;>
    simp [positiveCharacteristicExample, Derivation.leibniz, smul_eq_mul]

/-- The displayed nilpotence holds by a sparse square computation over
any commutative ring, with no characteristic-zero input. -/
private theorem positive_characteristic_matrix_pow_four_zero {R : Type*} [CommRing R] (a b : R) :
    let N : Matrix (Fin 4) (Fin 4) R := of ![![0, a, 0, 0], ![0, 0, a, 0], ![-b, 0, 0, a], ![0, b, 0, 0]]
    N ^ (4 : ℕ) = 0 := by
  dsimp only
  let N : Matrix (Fin 4) (Fin 4) R := of ![![0, a, 0, 0], ![0, 0, a, 0], ![-b, 0, 0, a], ![0, b, 0, 0]]
  let Q : Matrix (Fin 4) (Fin 4) R := of ![![0, 0, a ^ 2, 0], ![-(a * b), 0, 0, a ^ 2], ![0, 0, 0, 0], ![0, 0, a * b, 0]]
  have hN : N ^ 2 = Q := by
    rw [pow_two N]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [N, Q, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  have hQ : Q ^ 2 = 0 := by
    rw [pow_two Q]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [Q, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  change N ^ (2 * 2 : ℕ) = 0
  rw [pow_mul, hN, hQ]

theorem positiveCharacteristicExample_isHomogMap (p : ℕ) : IsHomogMap (positiveCharacteristicExample (K := K) p) (p + 1) := by
  have hA (i j : Fin 4) : (((X i : R₄) ^ p) * X j).IsHomogeneous (p + 1) := by
    simpa only [pow_one] using (isHomogeneous_X_pow (R := K) i p).mul (isHomogeneous_X_pow (R := K) j 1)
  intro i
  fin_cases i
  · exact hA 0 1
  · exact hA 0 2
  · exact (hA 0 3).sub (hA 1 0)
  · exact hA 1 1

/-- Evaluation at original scalar points separates all four components. -/
theorem positiveCharacteristicExample_componentsIndependent (p : ℕ) (hp : 0 < p) :
    ¬ ComponentsDependent (positiveCharacteristicExample (K := K) p) := by
  let H := positiveCharacteristicExample (K := K) p
  rintro ⟨c, hc, hrel⟩
  have h (v : Fin 4 → K) : ∑ i, c i * aeval v (H i) = 0 := by
    have he := congrArg (aeval v) hrel
    simpa only [map_sum, smul_eq_C_mul, map_mul, aeval_C, Algebra.algebraMap_self_apply, map_zero] using he
  have h1 : c 1 = 0 := by
    have he := h ![1, 0, 1, 0]
    simpa [H, positiveCharacteristicExample, Fin.sum_univ_four, zero_pow hp.ne'] using he
  have h2 : c 2 = 0 := by
    have he := h ![1, 0, 0, 1]
    simpa [H, positiveCharacteristicExample, Fin.sum_univ_four, zero_pow hp.ne'] using he
  have h3 : c 3 = 0 := by
    have he := h ![0, 1, 0, 0]
    simpa [H, positiveCharacteristicExample, Fin.sum_univ_four, zero_pow hp.ne'] using he
  have h0 : c 0 = 0 := by
    have he := h ![1, 1, 0, 0]
    simpa [H, positiveCharacteristicExample, Fin.sum_univ_four, h1, h2, h3] using he
  apply hc
  funext i
  fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3

/-- The example has a nilpotent Jacobian of rational rank exactly three
and independent components of the same homogeneous degree. -/
theorem positive_characteristic_counterexample_to_homogeneous_dependence
    (p : ℕ) (hp : 0 < p) [CharP K p] :
    let H := positiveCharacteristicExample (K := K) p
    IsHomogMap H (p + 1) ∧ IsNilpotent (jac H) ∧ polyRank (jac H) = 3 ∧ ¬ ComponentsDependent H := by
  let H := positiveCharacteristicExample (K := K) p
  let a := (X 0 : R₄) ^ p
  let b := (X 1 : R₄) ^ p
  have hJ : jac H = Matrix.of ![![0, a, 0, 0], ![0, 0, a, 0], ![-b, 0, 0, a], ![0, b, 0, 0]] :=
    positiveCharacteristicExample_jacobian p
  have hN : IsNilpotent (jac H) := ⟨4, hJ.symm ▸ positive_characteristic_matrix_pow_four_zero a b⟩
  let f := algebraMap R₄ (FractionRing R₄)
  let A := ((jac H).map f).submatrix Fin.castSucc (Fin.succ : Fin 3 → Fin 4)
  have hd : A.det = (f a) ^ 3 := by
    change (((jac H).map f).submatrix Fin.castSucc (Fin.succ : Fin 3 → Fin 4)).det = _
    rw [hJ, Matrix.det_fin_three]
    simp [Matrix.submatrix_apply, Matrix.map_apply, Matrix.of_apply]
    ring
  have ha : f a ≠ 0 := fun h => (pow_ne_zero p (X_ne_zero (R := K) 0))
    ((IsFractionRing.injective R₄ (FractionRing R₄)) (h.trans (map_zero f).symm))
  have hrank : A.rank = 3 := by
    rw [Matrix.rank_of_det_ne_zero (hd.symm ▸ pow_ne_zero 3 ha), Fintype.card_fin]
  have hle : 3 ≤ polyRank (jac H) := by
    have he := Matrix.rank_submatrix_le ((jac H).map f) Fin.castSucc (Fin.succ : Fin 3 → Fin 4)
    change A.rank ≤ polyRank (jac H) at he
    rw [hrank] at he
    exact he
  exact ⟨positiveCharacteristicExample_isHomogMap p, hN,
    le_antisymm (rank_at_most_three H hN) hle, positiveCharacteristicExample_componentsIndependent p hp⟩

end DimensionFourDependence
