import DimensionFourDependence.ParametricGraphCubic

/-! # The graph ruling denominator and cubic factor preserve exact scalar values -/

namespace DimensionFourDependence

open Matrix

variable {K F G : Type*} [Field K] [Field F] [Field G] [Algebra K F] [Algebra K G] {n : ℕ}

theorem parametricRulingDenominator_map (f : RatFunc K →ₐ[K] F) (g : F →ₐ[K] G)
    (A : Fin n → RatFunc K) (y : Fin n → F) :
    parametricRulingDenominator (g.comp f) A (fun i => g (y i)) = g (parametricRulingDenominator f A y) := by
  simp [parametricRulingDenominator, dotProduct, map_sum, map_mul]

theorem parametricGraphCubicCovector_map (f : RatFunc K →ₐ[K] F) (g : F →ₐ[K] G)
    (A : Fin n → RatFunc K) (y : Fin n → F) (i : Fin n) :
    parametricGraphCubicCovector (g.comp f) A (fun j => g (y j)) i = g (parametricGraphCubicCovector f A y i) := by
  simp [parametricGraphCubicCovector, parametricRulingDenominator_map, dotProduct,
    map_sum, map_mul, map_sub, map_div₀, map_pow, map_ofNat]

/-- The original rank-one quotient Hessian has exactly the square
of its ruling linear form as its quadratic self-value. -/
theorem matrixBilinearPairing_rank_one_quotient (a v : Fin n → F) (N : F) :
    matrixBilinearPairing (fun i j => -(a i * a j) / N) v v = -(a ⬝ᵥ v) ^ 2 / N := by
  simp only [matrixBilinearPairing, dotProduct, pow_two, div_eq_mul_inv, neg_mul,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- An isotropic direction of a nonzero rank-one quotient Hessian
lies in its actual ruling kernel. -/
theorem rank_one_quotient_isotropic_iff (a v : Fin n → F) (N : F) (hN : N ≠ 0) :
    matrixBilinearPairing (fun i j => -(a i * a j) / N) v v = 0 ↔ a ⬝ᵥ v = 0 := by
  rw [matrixBilinearPairing_rank_one_quotient]
  simp [hN]

end DimensionFourDependence
