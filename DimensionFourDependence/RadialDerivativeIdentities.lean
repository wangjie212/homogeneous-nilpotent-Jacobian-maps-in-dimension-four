import DimensionFourDependence.CoefficientEuler
import DimensionFourDependence.FiberEquations

/-! # The radial Hessian and cubic identities used in Section 3.2

Weight one for the last output makes its gradient weight zero and its
Hessian weight minus one. Contracting with the actual output coordinates
then gives the radial identities in the proof of Proposition 3.1.
-/

namespace DimensionFourDependence

variable {K : Type*} [Field K] [CharZero K]

/-- The gradient of a weight-one coefficient has weight zero. -/
theorem coefficientGradient_euler_zero
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h) (j : Fin 3) :
    coefficientEuler Y hY (coefficientPartial Y hY j h) = 0 := by
  have he := coefficientEuler_partial_weight Y hY h 1 (by simpa only [map_one, one_mul] using hh) j
  simpa only [sub_self, map_zero, zero_mul] using he

/-- The Hessian of a weight-one coefficient has weight minus one. -/
theorem coefficientHessian_euler_negative
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h) (i j : Fin 3) :
    coefficientEuler Y hY (coefficientHessian Y hY h i j) = -coefficientHessian Y hY h i j := by
  have he := coefficientEuler_partial_weight Y hY (coefficientPartial Y hY j h) 0
    (by simpa only [map_zero, zero_mul] using coefficientGradient_euler_zero Y hY h hh j) i
  simpa only [coefficientHessian, Matrix.of_apply, zero_sub, map_neg, map_one, neg_one_mul] using he

/-- Contracting the Hessian with the radial output direction gives zero. -/
theorem coefficientHessian_radial_contraction
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h) (j : Fin 3) :
    ∑ i, coefficientCoordinate (K := K) Y i * coefficientHessian Y hY h i j = 0 := by
  exact (coefficientEuler_apply Y hY (coefficientPartial Y hY j h)).symm.trans
    (coefficientGradient_euler_zero Y hY h hh j)

/-- Contracting the cubic tensor with the radial output direction gives minus the Hessian. -/
theorem coefficientCubicTensor_radial_contraction
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h) (j k : Fin 3) :
    ∑ i, coefficientCoordinate (K := K) Y i * coefficientCubicTensor Y hY h i j k =
      -coefficientHessian Y hY h j k := by
  exact (coefficientEuler_apply Y hY (coefficientHessian Y hY h j k)).symm.trans
    (coefficientHessian_euler_negative Y hY h hh j k)

/-- The stated bilinear identity `D²h[Y,v]=0`. -/
theorem coefficientHessian_radial_pairing
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h)
    (v : Fin 3 → coefficientField (K := K) Y) :
    ∑ i, ∑ j, coefficientHessian Y hY h i j * coefficientCoordinate (K := K) Y i * v j = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.sum_mul]
  have he : (∑ i, coefficientHessian Y hY h i j * coefficientCoordinate (K := K) Y i) = 0 := by
    simpa only [mul_comm] using coefficientHessian_radial_contraction Y hY h hh j
  rw [he, zero_mul]

/-- The stated trilinear identity `D³h[Y,v,w]=-D²h[v,w]`. -/
theorem coefficientCubicTensor_radial_pairing
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (hh : coefficientEuler Y hY h = h)
    (v w : Fin 3 → coefficientField (K := K) Y) :
    (∑ i, ∑ j, ∑ k, coefficientCubicTensor Y hY h i j k * coefficientCoordinate (K := K) Y i * v j * w k) =
      -(∑ j, ∑ k, coefficientHessian Y hY h j k * v j * w k) := by
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have he : (∑ i, coefficientCubicTensor Y hY h i j k * coefficientCoordinate (K := K) Y i) =
      -coefficientHessian Y hY h j k := by
    simpa only [mul_comm] using coefficientCubicTensor_radial_contraction Y hY h hh j k
  rw [he]
  ring

end DimensionFourDependence
