import DimensionFourDependence.TernaryGraphQuadraticInvariant
import DimensionFourDependence.FiberPolynomialGradients
import DimensionFourDependence.BoundaryLeadingEquations

/-! # The polynomial of the actual quadratic invariant -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {L : Type*} [Field L] [CharZero L] {n : ℕ}

/-- The formal second partials recover exactly the symmetric
coefficient matrix of the quadratic fiber polynomial. -/
theorem quadraticFiberPolynomial_second_partial
    (a : Fin n → L) (T : Matrix (Fin n) (Fin n) L) (q : L)
    (hT : ∀ i j, T i j = T j i) (i j : Fin n) :
    pderiv j (pderiv i (quadraticFiberPolynomial a T q)) = C (T i j) := by
  rw [quadraticFiberPolynomial_pderiv a T q hT i]
  change pderiv j (C (a i) + linearFormPolynomial (T i)) = _
  rw [map_add, pderiv_C, zero_add, linearFormPolynomial_pderiv]

/-- A nonzero symmetric quadratic array gives a nonzero polynomial. -/
theorem quadraticFiberPolynomial_ne_zero_of_symmetric_matrix
    (a : Fin n → L) (T : Matrix (Fin n) (Fin n) L) (q : L)
    (hT : ∀ i j, T i j = T j i) (hne : T ≠ 0) :
    quadraticFiberPolynomial a T q ≠ 0 := by
  intro h
  apply hne
  funext i j
  have he := quadraticFiberPolynomial_second_partial a T q hT i j
  rw [h, map_zero, map_zero] at he
  exact C_injective (Fin n) L (he.symm.trans (map_zero C).symm)

variable {K : Type*} [Field K] [CharZero K]
local notation "F" => FractionRing (MvPolynomial (Fin 3) K)
local notation "x" => (rationalCoordinate (K := K) (n := 3))

/-- The actual polynomial (3.6) over the coefficient field. -/
noncomputable def ternaryGraphQuadraticEquation
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (w s τ : coefficientField (K := K) Y) : MvPolynomial (Fin 2) (coefficientField (K := K) Y) :=
  quadraticFiberPolynomial (fun i => coefficientPartial Y hY i s)
    (of fun i j => coefficientPartial Y hY i (coefficientPartial Y hY j w)) τ

theorem ternaryGraphQuadraticEquation_aeval
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w s τ : coefficientField (K := K) Y)
    (hτ : (τ : F) = ternaryGraphQuadraticValue Y hY w s) :
    aeval (fun i : Fin 2 => x i.castSucc) (ternaryGraphQuadraticEquation Y hY w s τ) = 0 := by
  rw [ternaryGraphQuadraticEquation, quadraticFiberPolynomial_aeval]
  change ternaryGraphQuadraticValue Y hY w s - (τ : F) = 0
  rw [hτ, sub_self]

theorem ternaryGraphQuadraticEquation_ne_zero
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w s τ : coefficientField (K := K) Y)
    (hne : ternaryGraphHessian Y hY w ≠ 0) :
    ternaryGraphQuadraticEquation Y hY w s τ ≠ 0 := by
  let E := coefficientField (K := K) Y
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  apply quadraticFiberPolynomial_ne_zero_of_symmetric_matrix
  · intro i j
    exact coefficientPartials_commute Y hY i j w
  · intro h
    apply hne
    funext i j
    exact congrArg (algebraMap E F) (congrFun (congrFun h i) j)

theorem ternaryGraphQuadraticEquation_totalDegree_le
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w s τ : coefficientField (K := K) Y) :
    (ternaryGraphQuadraticEquation Y hY w s τ).totalDegree ≤ 2 :=
  quadraticFiberPolynomial_totalDegree _ _ _

end DimensionFourDependence
