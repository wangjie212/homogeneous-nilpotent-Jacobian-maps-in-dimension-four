import DimensionFourDependence.TernaryNormalFormTameWord
import DimensionFourDependence.TernaryNormalFormAffineChart
import DimensionFourDependence.TernaryNormalFormJacobian
import DimensionFourDependence.HomogeneousMatrixBlockNilpotence
import DimensionFourDependence.NormalizedFixedCoordinateReduction

/-! # Proposition 6.6: the homogenized ternary normal form is tame -/

namespace DimensionFourDependence.TernaryNormalForm

open Matrix MvPolynomial

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "t" => (X (Fin.last 3))

/-- The full polynomial Jacobian has fourth power zero. The active
block is cube zero because its cube is homogeneous and vanishes on
the actual final-coordinate chart. -/
theorem jac_perturbation4_fourth_power_zero (P : Polynomial K) {d : ℕ}
    (hm : 0 < P.natDegree) (hd : 4 * P.natDegree ≤ d) : jac (perturbation4 P d) ^ 4 = 0 := by
  let H := perturbation4 P d
  let B : Fin 3 → R₄ := fun i => H i.castSucc
  have hG : H = Fin.lastCases 0 B := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.lastCases_last]
      rfl
    · rw [Fin.lastCases_castSucc]
  let M := jac H
  have hz (j : Fin 4) : M (Fin.last 3) j = 0 := by
    change pderiv j (H (Fin.last 3)) = 0
    simp only [hG, Fin.lastCases_last, map_zero]
  have hmap : (M.submatrix Fin.castSucc Fin.castSucc).map
      (lastCoordinateDehomogenize (K := K) (n := 3)) = jac (perturbation3 P) := by
    change ((jac H).submatrix Fin.castSucc Fin.castSucc).map _ = _
    rw [hG, ← lastCoordinateDehomogenize_leading_jacobian]
    congr 1
    exact funext (dehomogenize_normal_perturbation4 P d)
  have hhom (i j : Fin 3) :
      ((M.submatrix Fin.castSucc Fin.castSucc) i j).IsHomogeneous (d - 1) :=
    (perturbation4_isHomogMap P hm hd i.castSucc).pderiv (i := j.castSucc)
  have hcube : (M.submatrix Fin.castSucc Fin.castSucc) ^ 3 = 0 := by
    apply homogeneous_matrix_pow_zero_of_dehomogenize_pow_zero _ hhom
    rw [hmap, jac_perturbation3_cube_zero]
  exact block_pow_succ_zero_of_leading_block_pow_zero M hz (by decide) hcube

/-- The explicit polynomial formulas are exactly the rational
expressions for `q` and `R` everywhere the last coordinate is invertible. -/
theorem q4_and_correction4_fraction_formulas
    {F : Type*} [Field F] [Algebra K F] (φ : R₄ →ₐ[K] F)
    (P : Polynomial K) {d : ℕ} (hm : 0 < P.natDegree) (hd : 4 * P.natDegree ≤ d)
    (ht : φ (t : R₄) ≠ 0) :
    φ (q4 P d) = φ t ^ (d - 1) * Polynomial.aeval (φ quadratic4 / φ t ^ 2) P ∧
    φ (correction4 P d) = φ t ^ d * (Polynomial.aeval (φ quadratic4 / φ t ^ 2) P) ^ 2 := by
  have hp : φ (numerator4 P) =
      φ t ^ (2 * P.natDegree) * Polynomial.aeval (φ quadratic4 / φ t ^ 2) P := by
    rw [numerator4, homogeneousParameterPolynomialValue_algHom, map_pow,
      homogeneousParameterPolynomialValue_fraction P le_rfl _ _ (pow_ne_zero _ ht), ← pow_mul]
  have h₁ : (d - 1 - 2 * P.natDegree) + (2 * P.natDegree) = d - 1 := by omega
  have h₂ : (d - 4 * P.natDegree) + (2 * P.natDegree) * 2 = d := by omega
  constructor
  · rw [q4, map_mul, map_pow, hp, ← mul_assoc, ← pow_add, h₁]
  · rw [correction4, map_mul, map_pow, map_pow, hp, mul_pow, ← pow_mul,
      ← mul_assoc, ← pow_add, h₂]

/-- **Proposition 6.6.** The polynomial representatives in (6.12)
give a tame automorphism, the displayed homogeneous perturbation and
an actual nilpotent Jacobian over the original coefficient field. -/
theorem proposition_6_6 (P : Polynomial K) {d : ℕ}
    (hm : 0 < P.natDegree) (hd : 4 * P.natDegree ≤ d) :
    normalFormAutomorphism4 P d ∈ Tame.subgroup K 4 ∧
    (∀ i, normalFormAutomorphism4 P d (X i) = X i + perturbation4 P d i) ∧
    IsHomogMap (perturbation4 P d) d ∧ IsNilpotent (jac (perturbation4 P d)) :=
  ⟨normalFormAutomorphism4_tame P d, normalFormAutomorphism4_X P hm hd,
    perturbation4_isHomogMap P hm hd, ⟨4, jac_perturbation4_fourth_power_zero P hm hd⟩⟩

end DimensionFourDependence.TernaryNormalForm
