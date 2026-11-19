import DimensionFourDependence.CubicRadialBaseChange

/-! # Radial covectors in the zero-invariant branch of Section 3.2

When both `c` and `q` vanish, the two covectors constructed from the
fiber invariants annihilate the actual radial output direction.
-/

namespace DimensionFourDependence

open Matrix

variable {K : Type*} [Field K] [CharZero K]

local notation "F" => FractionRing (MvPolynomial (Fin 4) K)

/-- The radial Hessian identity holds against arbitrary source-field vectors. -/
theorem fiberHessian_radial_pairing
    (Y : Fin 3 → F) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h)
    (x : Fin 3 → F) : matrixBilinearPairing (fiberHessian Y hY h) Y x = 0 := by
  exact matrixBilinearPairing_radical_map (coefficientHessian Y hY h)
    (coefficientCoordinate (K := K) Y) (coefficientHessian_radial_contraction Y hY h hh) x

/-- The cubic radial identity holds against arbitrary source-field vectors. -/
theorem fiberThirdDerivative_radial_pairing
    (Y : Fin 3 → F) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h)
    (x z : Fin 3 → F) :
    tensorTrilinearPairing (fiberThirdDerivative Y hY h) Y x z =
      -matrixBilinearPairing (fiberHessian Y hY h) x z := by
  exact tensorTrilinearPairing_radial_map (coefficientHessian Y hY h)
    (coefficientCubicTensor Y hY h) (coefficientCoordinate (K := K) Y)
    (coefficientCubicTensor_radial_contraction Y hY h hh) x z

/-- For `c=0`, the second covector annihilates the radial output. -/
theorem fiberSecondCovector_zero_radial
    (p : Equiv.Perm (Fin 4)) (Y : Fin 3 → F) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h) :
    fiberSecondCovector p Y hY h 0 ⬝ᵥ Y = 0 := by
  let x : Fin 3 → F := fun i => rationalCoordinate (K := K) (p i.castSucc)
  calc
    _ = matrixBilinearPairing (fiberHessian Y hY h) Y x := by
      simp only [fiberSecondCovector, map_zero, IntermediateField.coe_zero, zero_add,
        dotProduct, Finset.sum_mul, matrixBilinearPairing]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change fiberHessian Y hY h i j * x j * Y i = _
      ring
    _ = 0 := fiberHessian_radial_pairing Y hY h hh x

/-- When `c=q=0`, the third covector also annihilates the radial output. -/
theorem fiberThirdCovector_zero_radial
    (p : Equiv.Perm (Fin 4)) (Y : Fin 3 → F) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h)
    (hq : secondFiberInvariant p Y hY h 0 = 0) :
    fiberThirdCovector p Y hY h 0 0 ⬝ᵥ Y = 0 := by
  let x : Fin 3 → F := fun i => rationalCoordinate (K := K) (p i.castSucc)
  have he : (2 : F)⁻¹ * matrixBilinearPairing (fiberHessian Y hY h) x x = 0 := by
    simpa only [secondFiberInvariant, quadraticExpression, map_zero,
      IntermediateField.coe_zero, zero_mul, Finset.sum_const_zero, zero_add,
      matrixBilinearPairing] using hq
  calc
    _ = -(2 : F)⁻¹ * tensorTrilinearPairing (fiberThirdDerivative Y hY h) Y x x := by
      simp only [fiberThirdCovector, fiberHessian, Matrix.of_apply, map_zero,
        IntermediateField.coe_zero, zero_mul, Finset.sum_const_zero, sub_zero,
        zero_sub, dotProduct, tensorTrilinearPairing, neg_mul,
        Finset.sum_neg_distrib]
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [x]
      ring
    _ = 0 := by rw [fiberThirdDerivative_radial_pairing Y hY h hh x x]; simpa using he

end DimensionFourDependence
