import DimensionFourDependence.TernaryGraphQuadraticEquation
import DimensionFourDependence.LinearPolynomialConjugacy

/-! # A linear pullback of the leading quadratic transports its Hessian -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u v
set_option maxHeartbeats 2000000

variable {L : Type u} [Field L] {n : ℕ}

theorem quadraticFormPolynomial_aeval_eq_dotProduct
    {A : Type v} [CommRing A] [Algebra L A]
    (T : Matrix (Fin n) (Fin n) L) (x : Fin n → A) :
    aeval x (quadraticFormPolynomial T) = x ⬝ᵥ (T.map (algebraMap L A) *ᵥ x) := by
  simp only [quadraticFormPolynomial, map_sum, map_mul, aeval_C, aeval_X,
    dotProduct, mulVec, Matrix.map_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The quadratic form of a linear pullback has the conjugated
symmetric coefficient matrix. -/
theorem quadraticFormPolynomial_linear_pullback
    (A T : Matrix (Fin n) (Fin n) L) :
    aeval (linearPolynomialMap A) (quadraticFormPolynomial T) =
      quadraticFormPolynomial (Aᵀ * T * A) := by
  let R₀ := MvPolynomial (Fin n) L
  let x : Fin n → R₀ := X
  let f := algebraMap L R₀
  let B := A.map f
  let U := T.map f
  have h : linearPolynomialMap A = B *ᵥ x := rfl
  rw [h, quadraticFormPolynomial_aeval_eq_dotProduct]
  conv_rhs => rw [← aeval_X_left_apply (quadraticFormPolynomial (Aᵀ * T * A)),
    quadraticFormPolynomial_aeval_eq_dotProduct]
  have hMat : (Aᵀ * T * A).map f = Bᵀ * U * B := by
    simp only [Matrix.map_mul, Matrix.transpose_map, B, U]
  rw [hMat, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_transpose_mulVec, dotProduct_comm]

theorem quadraticFormPolynomial_smul (c : L) (T : Matrix (Fin n) (Fin n) L) :
    quadraticFormPolynomial (c • T) = C c * quadraticFormPolynomial T := by
  simp only [quadraticFormPolynomial, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

variable [CharZero L]

/-- The form determines every entry of a symmetric coefficient matrix
by its second formal partials in characteristic zero. -/
theorem quadraticFormPolynomial_symmetric_injective
    (T U : Matrix (Fin n) (Fin n) L)
    (hT : ∀ i j, T i j = T j i) (hU : ∀ i j, U i j = U j i)
    (h : quadraticFormPolynomial T = quadraticFormPolynomial U) : T = U := by
  have he : quadraticFiberPolynomial 0 T 0 = quadraticFiberPolynomial 0 U 0 := by
    simp only [quadraticFiberPolynomial, h]
  funext i j
  have hdiff := congrArg (fun p : MvPolynomial (Fin n) L => pderiv j (pderiv i p)) he
  change pderiv j (pderiv i (quadraticFiberPolynomial 0 T 0)) =
    pderiv j (pderiv i (quadraticFiberPolynomial 0 U 0)) at hdiff
  rw [quadraticFiberPolynomial_second_partial 0 T 0 hT,
    quadraticFiberPolynomial_second_partial 0 U 0 hU] at hdiff
  exact C_injective (Fin n) L hdiff

/-- An invertible linear pullback and a nonzero scalar multiple of
the form preserve precisely whether the Hessian is singular. -/
theorem symmetric_quadratic_form_linear_association_det_zero_iff
    (A T U : Matrix (Fin n) (Fin n) L) (hA : A.det ≠ 0) (c : L) (hc : c ≠ 0)
    (hT : ∀ i j, T i j = T j i) (hU : ∀ i j, U i j = U j i)
    (h : aeval (linearPolynomialMap A) (quadraticFormPolynomial U) =
      C c * quadraticFormPolynomial T) :
    U.det = 0 ↔ T.det = 0 := by
  have hUtr : Uᵀ = U := by
    funext i j
    exact hU j i
  have hBtr : (Aᵀ * U * A)ᵀ = Aᵀ * U * A := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hUtr, Matrix.mul_assoc]
  have hEq : Aᵀ * U * A = c • T := quadraticFormPolynomial_symmetric_injective _ _
    (fun i j => (congrFun (congrFun hBtr i) j).symm)
    (fun i j => by simp only [Matrix.smul_apply, hT i j])
    (by simpa only [quadraticFormPolynomial_linear_pullback, quadraticFormPolynomial_smul] using h)
  have he := congrArg Matrix.det hEq
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul] at he
  constructor
  · intro hz
    rw [hz, mul_zero, zero_mul] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hc)
  · intro hz
    rw [hz, mul_zero] at he
    exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hA)).resolve_left hA

end DimensionFourDependence
