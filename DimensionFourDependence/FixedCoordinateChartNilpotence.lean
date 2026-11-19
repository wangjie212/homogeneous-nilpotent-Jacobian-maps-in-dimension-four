import DimensionFourDependence.NormalizedFixedCoordinateReduction

/-! # Chart nilpotence from a full Jacobian with fixed final coordinate -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] {n : ℕ}

theorem normalizedFixedCoordinateChart_nilpotent_of_full
    (B : Fin n → MvPolynomial (Fin (n + 1)) K)
    (hN : IsNilpotent (jac (Fin.lastCases 0 B))) :
    IsNilpotent (jac (normalizedFixedCoordinateChart B)) := by
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (n + 1)) K) :=
    jac (Fin.lastCases 0 B)
  have hM : IsNilpotent M := hN
  have hz (j : Fin (n + 1)) : M (Fin.last n) j = 0 := by
    simp only [M, jac, Matrix.of_apply, Fin.lastCases_last, map_zero]
  have hlead : IsNilpotent (M.submatrix Fin.castSucc Fin.castSucc) :=
    leading_block_isNilpotent_of_last_row_zero (n := n) M hM hz
  exact normalizedFixedCoordinateChart_nilpotent (n := n) B hlead

end DimensionFourDependence
