import DimensionFourDependence.ImageRelationConjugacy
import DimensionFourDependence.StandardRulingQuadric

/-! # Transposition exchanges the two Segre rulings by actual source-target conjugacy -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]

/-- Transposition of the two-by-two Segre coordinate matrix. -/
def segreTransposeIndex : Equiv.Perm (Fin 4) := Equiv.swap 1 2

/-- Its constant source and target matrix. -/
def segreTransposeMatrix : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

theorem segreTransposeMatrix_square :
    segreTransposeMatrix (K := K) * segreTransposeMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [segreTransposeMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The actual polynomial automorphism of the original source. -/
noncomputable def segreTransposePolynomialEquiv :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  matrixPolynomialCoordinateEquiv segreTransposeMatrix segreTransposeMatrix
    segreTransposeMatrix_square segreTransposeMatrix_square

theorem segreTransposePolynomialEquiv_coordinate (i : Fin 4) :
    segreTransposePolynomialEquiv (X i : MvPolynomial (Fin 4) K) = X (segreTransposeIndex i) := by
  fin_cases i <;> simp [segreTransposePolynomialEquiv, matrixPolynomialCoordinateEquiv_apply,
    linearPolynomialPullback, linearPolynomialMap, segreTransposeMatrix, segreTransposeIndex, Fin.sum_univ_succ]
    <;> norm_num [Equiv.swap_apply_def]

theorem segreTransposePolynomialEquiv_involutive (z : MvPolynomial (Fin 4) K) :
    segreTransposePolynomialEquiv (segreTransposePolynomialEquiv z) = z :=
  matrix_linear_polynomial_substitution_inverse segreTransposeMatrix segreTransposeMatrix segreTransposeMatrix_square z

/-- Conjugation by transposition exchanges the two output rows and
simultaneously transposes the original source coordinates. -/
noncomputable def segreTransposeMap (P : Fin 4 → MvPolynomial (Fin 4) K) :
    Fin 4 → MvPolynomial (Fin 4) K :=
  linearPolynomialConjugate segreTransposeMatrix segreTransposeMatrix P

theorem segreTransposeMap_coordinate (P : Fin 4 → MvPolynomial (Fin 4) K) (i : Fin 4) :
    segreTransposeMap P i = segreTransposePolynomialEquiv (P (segreTransposeIndex i)) := by
  fin_cases i <;> simp [segreTransposeMap, linearPolynomialConjugate, segreTransposePolynomialEquiv,
    matrixPolynomialCoordinateEquiv_apply, segreTransposeMatrix, segreTransposeIndex, Fin.sum_univ_succ]
    <;> norm_num [Equiv.swap_apply_def]

theorem segreTransposeMap_substitution (P : Fin 4 → MvPolynomial (Fin 4) K)
    (z : MvPolynomial (Fin 4) K) :
    aeval (segreTransposeMap P) z = segreTransposePolynomialEquiv
      (aeval P (segreTransposePolynomialEquiv z)) := by
  have he := aeval_linearPolynomialPullback_conjugate segreTransposeMatrix segreTransposeMatrix
    (segreTransposeMatrix_square (K := K)) P (segreTransposePolynomialEquiv z)
  change aeval (segreTransposeMap P) (segreTransposePolynomialEquiv (segreTransposePolynomialEquiv z)) =
    segreTransposePolynomialEquiv (aeval P (segreTransposePolynomialEquiv z)) at he
  rwa [segreTransposePolynomialEquiv_involutive] at he

theorem segreTransposeMap_primitive (P : Fin 4 → MvPolynomial (Fin 4) K) (hP : IsPrimitiveVec P) :
    IsPrimitiveVec (segreTransposeMap P) := by
  intro q hq
  have heq : IsUnit (segreTransposePolynomialEquiv q) := hP _ (by
    intro i
    have he := map_dvd segreTransposePolynomialEquiv (hq (segreTransposeIndex i))
    simpa only [segreTransposeMap_coordinate, segreTransposePolynomialEquiv_involutive,
      segreTransposeIndex, Equiv.swap_apply_self] using he)
  have he := heq.map segreTransposePolynomialEquiv
  simpa only [segreTransposePolynomialEquiv_involutive] using he

theorem segreTransposeMap_ne_zero (P : Fin 4 → MvPolynomial (Fin 4) K) (hP : P ≠ 0) :
    segreTransposeMap P ≠ 0 := by
  intro he
  apply hP
  funext i
  apply segreTransposePolynomialEquiv.injective
  have hi := congrFun he (segreTransposeIndex i)
  simpa only [segreTransposeMap_coordinate, segreTransposeIndex, Equiv.swap_apply_self,
    Pi.zero_apply, map_zero] using hi

theorem segreTransposePolynomialEquiv_determinant :
    segreTransposePolynomialEquiv (standardRulingPolynomial (F := K)) = standardRulingPolynomial := by
  simp only [standardRulingPolynomial, map_sub, map_mul, segreTransposePolynomialEquiv_coordinate]
  norm_num [segreTransposeIndex, Equiv.swap_apply_def]
  ring

/-- Transposition preserves the actual determinant source prime. -/
theorem segreTransposePolynomialEquiv_mem_determinant_prime (z : MvPolynomial (Fin 4) K) :
    segreTransposePolynomialEquiv z ∈ Ideal.span {standardRulingPolynomial (F := K)} ↔
      z ∈ Ideal.span {standardRulingPolynomial (F := K)} := by
  have hd (a : MvPolynomial (Fin 4) K)
      (ha : standardRulingPolynomial (F := K) ∣ a) :
      standardRulingPolynomial (F := K) ∣ segreTransposePolynomialEquiv a := by
    simpa only [segreTransposePolynomialEquiv_determinant] using map_dvd segreTransposePolynomialEquiv ha
  simp only [Ideal.mem_span_singleton]
  constructor
  · intro hz
    simpa only [segreTransposePolynomialEquiv_involutive] using hd _ hz
  · exact hd z

end DimensionFourDependence
