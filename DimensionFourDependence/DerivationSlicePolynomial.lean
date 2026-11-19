import DimensionFourDependence.ConstantField
import Mathlib.Algebra.Polynomial.Degree.Units

/-! # Polynomial expressions over the constants of a derivation with a slice -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 1800000

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- An element with derivative one is transcendental over the actual
constant field. -/
theorem derivation_slice_transcendental
    (D : Derivation K F F) (x : F) (hx : D x = 1) :
    Transcendental (derivationConstants D) x := by
  intro h
  have hz := derivation_zero_of_isAlgebraic
    (derivationOverConstantSubfield D (derivationConstants D) le_rfl) x h
  exact one_ne_zero (hx.symm.trans hz)

/-- A product of two polynomial values in the slice equal to one
forces both representing polynomials to be constant. -/
theorem derivation_slice_product_one_forces_constant
    (D : Derivation K F F) (x : F) (hx : D x = 1)
    (P Q : Polynomial (derivationConstants D))
    (h : Polynomial.aeval x P * Polynomial.aeval x Q = 1) (i : ℕ) (hi : i ≠ 0) :
    Q.coeff i = 0 := by
  have hEval := (transcendental_iff_injective.mp (derivation_slice_transcendental D x hx))
  have hOne : Q * P = 1 := by
    apply hEval
    simpa only [map_mul, map_one, mul_comm] using h
  have hu : IsUnit Q := IsUnit.of_mul_eq_one P hOne
  have hDeg := Polynomial.natDegree_eq_zero_of_isUnit hu
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

omit [CharZero K] in
/-- Once each source coordinate is polynomial in a slice over the
constant field, every original source polynomial has such an expression. -/
theorem polynomial_values_are_polynomial_in_derivation_slice
    {n : ℕ} (D : Derivation K F F) (x : F) (Z : Fin n → F)
    (hZ : ∀ i, ∃ P : Polynomial (derivationConstants D), Polynomial.aeval x P = Z i)
    (R : MvPolynomial (Fin n) K) :
    ∃ P : Polynomial (derivationConstants D), Polynomial.aeval x P = MvPolynomial.aeval Z R := by
  induction R using MvPolynomial.induction_on with
  | C c =>
    refine ⟨Polynomial.C (algebraMap K (derivationConstants D) c), ?_⟩
    rw [Polynomial.aeval_C, MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply]
  | add P Q hp hq =>
    obtain ⟨A, hA⟩ := hp
    obtain ⟨B, hB⟩ := hq
    exact ⟨A + B, by rw [map_add, map_add, hA, hB]⟩
  | mul_X P i hp =>
    obtain ⟨A, hA⟩ := hp
    obtain ⟨B, hB⟩ := hZ i
    exact ⟨A * B, by rw [map_mul, map_mul, hA, hB, MvPolynomial.aeval_X]⟩

omit [CharZero K] in
/-- When the middle coordinate has affine derivative in the slice,
it is quadratic in the slice with coefficients in the constant field. -/
theorem derivation_slice_integrates_affine_value
    (D : Derivation K F F) (x y b c : F) (hx : D x = 1)
    (hb : D b = 0) (hc : D c = 0) (hy : D y = b + 2 * c * x) :
    ∃ a : F, D a = 0 ∧ y = a + b * x + c * x ^ 2 := by
  refine ⟨y - b * x - c * x ^ 2, ?_, by ring⟩
  simp only [map_sub, D.leibniz, D.leibniz_pow, smul_eq_mul, hb, hc, hx, hy]
  norm_num
  ring

end DimensionFourDependence
