import DimensionFourDependence.CoefficientChainRule
import DimensionFourDependence.VerticalDerivation

/-! # The Jacobian factorization `N = E B` in Lemma 2.2 -/

namespace DimensionFourDependence

open Matrix

/-- Multiplying a matrix with an identity block and one additional row. -/
theorem snoc_identity_mul {F : Type*} [Field F] {n m : ℕ}
    (B : Matrix (Fin n) (Fin m) F) (g : Fin n → F) :
    Matrix.of (Fin.snoc B (g ᵥ* B)) =
      Matrix.of (Fin.snoc (1 : Matrix (Fin n) (Fin n) F) g) * B := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [Fin.snoc, Matrix.mul_apply, vecMul, dotProduct]
  · simp [Fin.snoc, Matrix.mul_apply, Matrix.one_apply]

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

omit [CharZero K] in
/-- Appending an output appends its derivative row to the Jacobian. -/
theorem rationalJacobian_snoc {m r : ℕ}
    (Y : Fin m → FractionRing (MvPolynomial (Fin r) K))
    (h : FractionRing (MvPolynomial (Fin r) K)) :
    rationalJacobian (Fin.snoc Y h) =
      Fin.snoc (rationalJacobian Y) (fun j => rationalPartial (K := K) j h) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    simp [rationalJacobian, Fin.snoc]

/-- The gradient of the last output with respect to the independent outputs. -/
noncomputable def fiberGradient
    (Y : Fin n → FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hY : AlgebraicIndependent K Y) (h : coefficientField (K := K) Y) :
    Fin n → FractionRing (MvPolynomial (Fin (n + 1)) K) :=
  fun i => (coefficientPartial (K := K) Y hY i h : FractionRing (MvPolynomial (Fin (n + 1)) K))

/-- The tangent embedding `E = (I, ∇hᵀ)ᵀ`. -/
noncomputable def fiberFrame
    (Y : Fin n → FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hY : AlgebraicIndependent K Y) (h : coefficientField (K := K) Y) :
    Matrix (Fin (n + 1)) (Fin n) (FractionRing (MvPolynomial (Fin (n + 1)) K)) :=
  Fin.snoc (fun i j => if i = j then 1 else 0) (fiberGradient Y hY h)

/-- The normal covector `(-∇hᵀ, 1)`. -/
noncomputable def fiberNormal
    (Y : Fin n → FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hY : AlgebraicIndependent K Y) (h : coefficientField (K := K) Y) :
    Fin (n + 1) → FractionRing (MvPolynomial (Fin (n + 1)) K) :=
  Fin.snoc (fun i => -fiberGradient Y hY h i) 1

/-- Differentiating the algebraic last output gives the actual matrix
factorization from the paper, over the source rational function field. -/
theorem fiber_jacobian_factorization
    (Y : Fin n → FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hY : AlgebraicIndependent K Y) (h : coefficientField (K := K) Y) :
    rationalJacobian (Fin.snoc Y (h : FractionRing (MvPolynomial (Fin (n + 1)) K))) =
      fiberFrame Y hY h * rationalJacobian Y := by
  have hlast : (fun j => rationalPartial (K := K) j
      (h : FractionRing (MvPolynomial (Fin (n + 1)) K))) =
        fiberGradient Y hY h ᵥ* rationalJacobian Y := by
    funext j
    rw [coefficient_chain_rule Y hY]
    simp only [vecMul, dotProduct, fiberGradient, rationalJacobian, Matrix.of_apply, mul_comm]
  rw [rationalJacobian_snoc, hlast]
  exact snoc_identity_mul (rationalJacobian Y) (fiberGradient Y hY h)

/-- The displayed normal annihilates the tangent embedding. -/
theorem fiberNormal_frame_zero
    (Y : Fin n → FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hY : AlgebraicIndependent K Y) (h : coefficientField (K := K) Y) :
    fiberNormal Y hY h ᵥ* fiberFrame Y hY h = 0 := by
  funext j
  simp [vecMul, dotProduct, Fin.sum_univ_castSucc, fiberNormal, fiberFrame]

/-- Hence the normal is a left-kernel covector of the full Jacobian. -/
theorem fiberNormal_jacobian_zero
    (Y : Fin n → FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hY : AlgebraicIndependent K Y) (h : coefficientField (K := K) Y) :
    fiberNormal Y hY h ᵥ*
      rationalJacobian (Fin.snoc Y (h : FractionRing (MvPolynomial (Fin (n + 1)) K))) = 0 := by
  rw [fiber_jacobian_factorization Y hY h, ← vecMul_vecMul,
    fiberNormal_frame_zero, zero_vecMul]

end DimensionFourDependence
