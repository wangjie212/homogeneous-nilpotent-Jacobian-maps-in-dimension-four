import DimensionFourDependence.QuadraticHessianLinearTransport
import DimensionFourDependence.BinaryQuadraticInfinityDirections

/-! # Axis directions identify the diagonal entries of a quadratic form -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u v
set_option maxHeartbeats 1500000

variable {L : Type u} {A : Type v} [Field L] [Field A] [Algebra L A] {n : ℕ}

/-- A nonzero zero of the quadratic form along an axis forces the
corresponding diagonal entry to vanish in the original field. -/
theorem quadraticFormPolynomial_nonzero_axis_root_diagonal_zero
    (T : Matrix (Fin n) (Fin n) L) (j : Fin n) (e : Fin n → A)
    (hj : e j ≠ 0) (hs : ∀ i, i ≠ j → e i = 0)
    (he : aeval e (quadraticFormPolynomial T) = 0) :
    T j j = 0 := by
  rw [quadraticFormPolynomial_aeval_eq_dotProduct] at he
  have hx : e = Pi.single j (e j) := by
    funext i
    by_cases h : i = j
    · subst i
      simp
    · simp [Pi.single_apply, h, hs i h]
  rw [hx, single_dotProduct, Matrix.mulVec] at he
  change (e j) * ((T.map (algebraMap L A)).row j ⬝ᵥ Pi.single j (e j)) = 0 at he
  rw [dotProduct_single] at he
  change e j * (algebraMap L A (T j j) * e j) = 0 at he
  apply (algebraMap L A).injective
  rw [map_zero]
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hj)).resolve_right hj

/-- A symmetric two-by-two matrix evaluates to the scalar binary
expression with its original diagonal and mixed coefficients. -/
theorem quadraticFormPolynomial_aeval_fin_two_binary_value
    (T : Matrix (Fin 2) (Fin 2) L) (hT : T 1 0 = T 0 1) (e : Fin 2 → A) :
    aeval e (quadraticFormPolynomial T) =
      binaryQuadraticValue (algebraMap L A (T 0 0)) (algebraMap L A (T 0 1))
        (algebraMap L A (T 1 1)) e := by
  simp only [quadraticFormPolynomial, binaryQuadraticValue, Fin.sum_univ_two, hT]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  ring

end DimensionFourDependence
