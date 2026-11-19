import DimensionFourDependence.TernaryGraphPlaneInvariant
import DimensionFourDependence.SecondInvariant

/-! # Differentiating the exact affine plane equation of the ternary curve -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 1700000

variable {K : Type*} [Field K] [CharZero K]
local notation "F" => FractionRing (MvPolynomial (Fin 3) K)
local notation "x" => (rationalCoordinate (K := K) (n := 3))

noncomputable def ternaryGraphHessian
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (w : coefficientField (K := K) Y) : Matrix (Fin 2) (Fin 2) F :=
  fun i j => (coefficientPartial Y hY i (coefficientPartial Y hY j w) : F)

theorem ternaryGraphHessian_symmetric (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (w : coefficientField (K := K) Y) (i j : Fin 2) :
    ternaryGraphHessian Y hY w i j = ternaryGraphHessian Y hY w j i :=
  congrArg (fun a : coefficientField (K := K) Y => (a : F)) (coefficientPartials_commute Y hY i j w)

noncomputable def ternaryGraphAffineGradient
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w s : coefficientField (K := K) Y)
    (i : Fin 2) : F :=
  (coefficientPartial Y hY i s : F) +
    ∑ j : Fin 2, ternaryGraphHessian Y hY w i j * x j.castSucc

/-- The differentiated equation (3.5) holds for each source derivation
and the actual algebraic coefficient derivatives. -/
theorem ternaryGraphPlane_derivation
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w s : coefficientField (K := K) Y)
    (hs : (s : F) = ternaryGraphPlaneValue Y hY w) (D : Derivation K F F) :
    D (x 2) - (∑ i : Fin 2, ternaryGraphGradient Y hY w i * D (x i.castSucc)) =
      ∑ i : Fin 2, ternaryGraphAffineGradient Y hY w s i * D (Y i) := by
  have ht : (s : F) = x 2 - ∑ i : Fin 2, ternaryGraphGradient Y hY w i * x i.castSucc := by
    rw [hs, ternaryGraphPlaneValue, Fin.sum_univ_two]
    change x 2 - ternaryGraphGradient Y hY w 0 * x 0 - ternaryGraphGradient Y hY w 1 * x 1 =
      x 2 - (ternaryGraphGradient Y hY w 0 * x 0 + ternaryGraphGradient Y hY w 1 * x 1)
    ring
  have he := linear_fiber_equation_derivative D (fun i : Fin 2 => x i.castSucc)
    (ternaryGraphGradient Y hY w) (x 2) (s : F) ht
  have hG (j : Fin 2) : D (ternaryGraphGradient Y hY w j) =
      ∑ i : Fin 2, ternaryGraphHessian Y hY w i j * D (Y i) := by
    change D (coefficientPartial Y hY j w : F) = _
    rw [coefficient_chain_rule Y hY D]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [he, coefficient_chain_rule Y hY D s]
  have hsD : (∑ i : Fin 2, D (Y i) * (coefficientPartial Y hY i s : F)) =
      ∑ i : Fin 2, (coefficientPartial Y hY i s : F) * D (Y i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hsD]
  simp_rw [hG]
  exact collect_affine_coefficient_derivatives _ _ _ _

theorem ternaryGraphPlane_coordinate_partials
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w s : coefficientField (K := K) Y)
    (hs : (s : F) = ternaryGraphPlaneValue Y hY w) (j : Fin 3) :
    ternaryGraphAffineGradient Y hY w s 0 * ternaryRationalGradient (Y 0) j +
      ternaryGraphAffineGradient Y hY w s 1 * ternaryRationalGradient (Y 1) j =
    ![-ternaryGraphGradient Y hY w 0, -ternaryGraphGradient Y hY w 1, 1] j := by
  have he := (ternaryGraphPlane_derivation Y hY w s hs (rationalPartial (K := K) j)).symm
  rw [Fin.sum_univ_two, Fin.sum_univ_two, rationalPartial_coordinate,
    rationalPartial_coordinate, rationalPartial_coordinate] at he
  fin_cases j <;> simpa [ternaryRationalGradient] using he

end DimensionFourDependence
