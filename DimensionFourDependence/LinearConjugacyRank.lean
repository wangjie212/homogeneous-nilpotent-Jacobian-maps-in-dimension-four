import DimensionFourDependence.LinearPolynomialConjugacy

/-! # The actual rational Jacobian rank survives linear conjugacy

The source automorphism identifies every original rational Jacobian
entry. Its field embedding preserves matrix rank; the two inverse
constant matrix factors preserve rank on the target and source sides.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] {n : ℕ}

/-- Source and target coordinate conjugacy preserves the Jacobian rank
over the actual rational function field of the original source. -/
theorem linearPolynomialConjugate_polyRank
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K) :
    polyRank (jac (linearPolynomialConjugate T S H)) = polyRank (jac H) := by
  classical
  let R := MvPolynomial (Fin n) K
  let F := FractionRing R
  let f := matrixSourceFractionEquiv T S hTS hST
  let a : Matrix (Fin n) (Fin n) F := T.map (algebraMap K F)
  let b : Matrix (Fin n) (Fin n) F := S.map (algebraMap K F)
  let M : Matrix (Fin n) (Fin n) F := (jac H).map (algebraMap R F)
  have hab : a * b = 1 := by
    dsimp only [a, b]
    rw [← Matrix.map_mul, hTS]
    ext i j
    simp [Matrix.one_apply]
  have hba : b * a = 1 := by
    dsimp only [a, b]
    rw [← Matrix.map_mul, hST]
    ext i j
    simp [Matrix.one_apply]
  have ha : IsUnit a := IsUnit.of_mul_eq_one b hab
  have hb : IsUnit b := IsUnit.of_mul_eq_one a hba
  have hmap : ((jac H).map (aeval (linearPolynomialMap T))).map (algebraMap R F) =
      M.map f.toRingHom := by
    ext i j
    exact (matrixSourceFractionEquiv_polynomial T S hTS hST (jac H i j)).symm
  have heq : (jac (linearPolynomialConjugate T S H)).map (algebraMap R F) =
      b * M.map f.toRingHom * a := by
    rw [jac_linearPolynomialConjugate, Matrix.map_mul, Matrix.map_mul, hmap]
    rfl
  change ((jac (linearPolynomialConjugate T S H)).map (algebraMap R F)).rank = M.rank
  rw [heq, Matrix.rank_mul_eq_left_of_isUnit_det a _ ((Matrix.isUnit_iff_isUnit_det a).mp ha),
    Matrix.rank_mul_eq_right_of_isUnit_det b _ ((Matrix.isUnit_iff_isUnit_det b).mp hb)]
  exact matrix_rank_field_map f.toRingHom M

end DimensionFourDependence
