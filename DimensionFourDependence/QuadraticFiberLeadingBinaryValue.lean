import DimensionFourDependence.TernaryGraphQuadraticEquation
import DimensionFourDependence.BinaryQuadraticInfinityDirections

/-! # The ternary conic's directions are zeros of its binary output Hessian -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u v
set_option maxHeartbeats 1550000

variable {L : Type u} {A : Type v} [Field L] [CharZero L] [Field A] [Algebra L A]

/-- The leading quadratic value is half the Hessian pairing, with
its coefficients transported to any field extension. -/
theorem leading_quadraticFiberPolynomial_aeval_fin_two
    (a : Fin 2 → L) (T : Matrix (Fin 2) (Fin 2) L) (q : L)
    (hT : T 1 0 = T 0 1) (e : Fin 2 → A) :
    2 * aeval e (homogeneousComponent 2 (quadraticFiberPolynomial a T q)) =
      binaryQuadraticValue (algebraMap L A (T 0 0)) (algebraMap L A (T 0 1))
        (algebraMap L A (T 1 1)) e := by
  let : CharZero A := charZero_of_injective_algebraMap (algebraMap L A).injective
  rw [quadraticFiberPolynomial_leading_component, map_mul, aeval_C, map_inv₀, map_ofNat,
    ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
  simp only [quadraticFormPolynomial, binaryQuadraticValue, Fin.sum_univ_two, hT]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  ring

variable {K : Type u} [Field K] [CharZero K]
local notation "F" => FractionRing (MvPolynomial (Fin 3) K)

/-- The vanishing of the conic at infinity is precisely vanishing
of the binary quadratic form from the two output coordinate derivatives. -/
theorem ternaryGraphQuadraticEquation_leading_zero_iff_binaryHessian
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) (w s τ : coefficientField (K := K) Y)
    [Algebra (coefficientField (K := K) Y) A] (e : Fin 2 → A) :
    aeval e (homogeneousComponent 2 (ternaryGraphQuadraticEquation Y hY w s τ)) = 0 ↔
      binaryQuadraticValue
        (algebraMap (coefficientField (K := K) Y) A (coefficientPartial Y hY 0 (coefficientPartial Y hY 0 w)))
        (algebraMap (coefficientField (K := K) Y) A (coefficientPartial Y hY 0 (coefficientPartial Y hY 1 w)))
        (algebraMap (coefficientField (K := K) Y) A (coefficientPartial Y hY 1 (coefficientPartial Y hY 1 w)))
        e = 0 := by
  let E := coefficientField (K := K) Y
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  let : CharZero A := charZero_of_injective_algebraMap (algebraMap E A).injective
  have h := leading_quadraticFiberPolynomial_aeval_fin_two
    (fun i => coefficientPartial Y hY i s)
    (Matrix.of fun i j => coefficientPartial Y hY i (coefficientPartial Y hY j w)) τ
    (coefficientPartials_commute Y hY 1 0 w) e
  simp only [Matrix.of_apply] at h
  rw [← h, ternaryGraphQuadraticEquation]
  exact ⟨fun hz => by rw [hz, mul_zero], fun hz => (mul_eq_zero.mp hz).resolve_left two_ne_zero⟩

end DimensionFourDependence
