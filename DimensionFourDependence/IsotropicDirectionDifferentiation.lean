import DimensionFourDependence.NormalizedPlaneCoordinates

/-! # Differentiating an isotropic Hessian direction

Vanishing of the cubic self-contraction makes the derivative orthogonal
to the direction. Rank two and the coordinate normalization then force
the derivative of the direction itself to vanish.
-/

namespace DimensionFourDependence

open Matrix

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- Differentiate the symmetric quadratic pairing of a varying vector. -/
theorem matrixBilinearPairing_derivation
    (D : Derivation K F F) (T : Matrix (Fin n) (Fin n) F) (hT : ∀ i j, T i j = T j i)
    (Z : Fin n → F) :
    D (matrixBilinearPairing T Z Z) =
      (∑ i, ∑ j, D (T i j) * Z i * Z j) +
        2 * matrixBilinearPairing T (fun i => D (Z i)) Z := by
  have he (i j : Fin n) : D (T i j * Z i * Z j) =
      D (T i j) * Z i * Z j + T i j * D (Z i) * Z j + T i j * Z i * D (Z j) := by
    simp only [D.leibniz, smul_eq_mul]
    ring
  have hs : (∑ i, ∑ j, T i j * Z i * D (Z j)) =
      ∑ i, ∑ j, T i j * D (Z i) * Z j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hT j i]
    ring
  simp only [matrixBilinearPairing, map_sum, he, Finset.sum_add_distrib]
  rw [hs]
  ring

/-- If the cubic coefficient-variation term vanishes, an isotropic
direction's derivative is orthogonal to that direction. -/
theorem isotropic_direction_derivative_orthogonal [CharZero F]
    (D : Derivation K F F) (T : Matrix (Fin n) (Fin n) F) (hT : ∀ i j, T i j = T j i)
    (Z : Fin n → F) (hZ : matrixBilinearPairing T Z Z = 0)
    (hcoef : (∑ i, ∑ j, D (T i j) * Z i * Z j) = 0) :
    matrixBilinearPairing T (fun i => D (Z i)) Z = 0 := by
  have he := matrixBilinearPairing_derivation D T hT Z
  rw [hZ, map_zero, hcoef, zero_add] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

/-- The normalization removes the entire derivative of an isotropic
direction for a rank-two radial Hessian. -/
theorem normalized_isotropic_direction_derivative_zero [CharZero F]
    (D : Derivation K F F) (T : Matrix (Fin 3) (Fin 3) F) (hT : ∀ i j, T i j = T j i)
    (hrank : T.rank = 2) (Y Z : Fin 3 → F) (hY : T *ᵥ Y = 0)
    (a b : Fin 3) (hYa : Y a ≠ 0) (hZa : Z a = 0) (hZb : Z b = 1)
    (hZ : matrixBilinearPairing T Z Z = 0)
    (hcoef : (∑ i, ∑ j, D (T i j) * Z i * Z j) = 0) :
    (fun i => D (Z i)) = 0 := by
  apply normalized_radial_plane_vector_zero Y Z _ a b hYa hZa hZb
  · apply rank_two_isotropic_orthogonal_plane T hT hrank Y Z
      (normalized_radial_direction_independent Y Z a b hYa hZa hZb) hY hZ
    exact isotropic_direction_derivative_orthogonal D T hT Z hZ hcoef
  · rw [hZa, map_zero]
  · rw [hZb, D.map_one_eq_zero]

end DimensionFourDependence
