import DimensionFourDependence.BinaryBlockNilpotence
import DimensionFourDependence.HomogeneousDifferentialDependence

/-! # The zero vertical-derivative branch of Proposition 2.1 -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K

theorem componentsDependent_of_first_pair_relation
    (H : Fin 4 → R₀) (c t : K) (hct : c ≠ 0 ∨ t ≠ 0)
    (he : c • H 0 + t • H 1 = 0) : ComponentsDependent H := by
  refine ⟨![c, t, 0, 0], ?_, ?_⟩
  · intro hz
    have hc := congrFun hz 0
    have ht := congrFun hz 1
    exact hct.elim (fun h => h hc) (fun h => h ht)
  · simpa [Fin.sum_univ_succ] using he

/-- When the first two outputs have no vertical derivatives, their
actual leading binary Jacobian block inherits nilpotence. Its vanishing
determinant and the original Euler identities construct a constant
component relation, including zero-gradient cases. -/
theorem nilpotent_binary_output_pair_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H))
    (hzero : ∀ i : Fin 2, pderiv 2 (H (i.castAdd 2)) = 0 ∧ pderiv 3 (H (i.castAdd 2)) = 0) :
    ComponentsDependent H := by
  have hcast0 : (0 : Fin 2).castAdd 2 = (0 : Fin 4) := by decide
  have hcast1 : (1 : Fin 2).castAdd 2 = (1 : Fin 4) := by decide
  have hblock := leading_binary_block_isNilpotent (jac H) hN hzero
  have hdet : ((jac H).submatrix (Fin.castAdd 2) (Fin.castAdd 2)).det = 0 := by
    obtain ⟨k, hk⟩ := hblock
    have he := congrArg Matrix.det hk
    rw [Matrix.det_pow, Matrix.det_zero] at he
    exact isNilpotent_iff_eq_zero.mp ⟨k, he⟩
  have hdet' : pderiv 0 (H 0) * pderiv 1 (H 1) - pderiv 1 (H 0) * pderiv 0 (H 1) = 0 := by
    simpa only [Matrix.det_fin_two, Matrix.submatrix_apply, jac, Matrix.of_apply, hcast0, hcast1] using hdet
  have hz0 := hzero 0
  have hz1 := hzero 1
  change pderiv 2 (H 0) = 0 ∧ pderiv 3 (H 0) = 0 at hz0
  change pderiv 2 (H 1) = 0 ∧ pderiv 3 (H 1) = 0 at hz1
  have hreduce (a b : R₀) (hab : a ≠ 0 ∨ b ≠ 0)
      (h0 : a * pderiv 0 (H 0) + b * pderiv 0 (H 1) = 0)
      (h1 : a * pderiv 1 (H 0) + b * pderiv 1 (H 1) = 0) : ComponentsDependent H := by
    have hgrad (i : Fin 4) : a * pderiv i (H 0) + b * pderiv i (H 1) = 0 := by
      fin_cases i
      · exact h0
      · exact h1
      · change a * pderiv (2 : Fin 4) (H 0) + b * pderiv 2 (H 1) = 0
        simp only [hz0.1, hz1.1, mul_zero, add_zero]
      · change a * pderiv (3 : Fin 4) (H 0) + b * pderiv 3 (H 1) = 0
        simp only [hz0.2, hz1.2, mul_zero, add_zero]
    obtain ⟨c, t, hct, he⟩ := constant_relation_of_homogeneous_differential_relation
      (H 0) (H 1) a b hd (hH 0) (hH 1) hab hgrad
    exact componentsDependent_of_first_pair_relation H c t hct he
  by_cases h0 : pderiv 0 (H 0) = 0
  · by_cases h1 : pderiv 1 (H 0) = 0
    · have he := (hH 0).sum_X_mul_pderiv
      simp [Fin.sum_univ_succ, h0, h1, hz0] at he
      have hH0 : H 0 = 0 := he.resolve_left hd.ne'
      exact componentsDependent_of_first_pair_relation H 1 0 (Or.inl one_ne_zero) (by simp [hH0])
    · apply hreduce (pderiv 1 (H 1)) (-pderiv 1 (H 0)) (Or.inr (neg_ne_zero.mpr h1))
      · linear_combination hdet'
      · ring
  · apply hreduce (pderiv 0 (H 1)) (-pderiv 0 (H 0)) (Or.inr (neg_ne_zero.mpr h0))
    · ring
    · linear_combination -hdet'

end DimensionFourDependence
