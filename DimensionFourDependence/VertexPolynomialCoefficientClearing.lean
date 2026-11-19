import DimensionFourDependence.TransverseSourceFractionField

/-! # Vertex polynomials have a transverse source common denominator

Clearing a polynomial's finitely many coefficients in the actual
transverse fraction field constructs a nonzero ternary denominator.
After restoring the original coordinates, its product with the polynomial
value is an original four-variable polynomial.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

local notation "A₀" => MvPolynomial (Fin 3) K
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "L₀" => transverseSourceField K
local notation "w₀" => rationalCoordinate (K := K) (Fin.last 3)

/-- Clearing the actual coefficient field supplies a transverse source
polynomial common denominator for every vertex polynomial. -/
theorem vertex_polynomial_value_clears_transverse_source_denominator
    (U : Polynomial L₀) :
    ∃ c : A₀, c ≠ 0 ∧ ∃ V : R₀,
      algebraMap R₀ S₀ (rename Fin.castSucc c) * Polynomial.aeval w₀ U =
        algebraMap R₀ S₀ V := by
  classical
  let : Algebra A₀ L₀ := (aeval (transverseSourceCoordinate K)).toRingHom.toAlgebra
  let : IsFractionRing A₀ L₀ := transverseSourceCoordinate_isFractionRing K
  let N : Polynomial A₀ := IsLocalization.integerNormalization (nonZeroDivisors A₀) U
  obtain ⟨c, hc, hN⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A₀) U
  have hvalue (P : Polynomial A₀) :
      algebraMap R₀ S₀ (Polynomial.eval₂ (rename Fin.castSucc).toRingHom (X (Fin.last 3)) P) =
        Polynomial.aeval w₀ (P.map (algebraMap A₀ L₀)) := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
        simp only [Polynomial.eval₂_add, map_add, Polynomial.map_add] at *
        exact congrArg₂ (· + ·) hP hQ
    | monomial n a =>
        simp only [Polynomial.eval₂_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial,
          map_mul, map_pow]
        change algebraMap R₀ S₀ (rename Fin.castSucc a) * w₀ ^ n =
          algebraMap L₀ S₀ (aeval (transverseSourceCoordinate K) a) * w₀ ^ n
        rw [transverseSourceCoordinate_aeval_source_value]
  have hscaled : N.map (algebraMap A₀ L₀) =
      Polynomial.C (algebraMap A₀ L₀ c) * U := by
    simpa only [← algebraMap_smul L₀ c U, Polynomial.smul_eq_C_mul] using hN
  refine ⟨c, mem_nonZeroDivisors_iff_ne_zero.mp hc,
    Polynomial.eval₂ (rename Fin.castSucc).toRingHom (X (Fin.last 3)) N, ?_⟩
  rw [hvalue, hscaled, map_mul, Polynomial.aeval_C]
  change algebraMap R₀ S₀ (rename Fin.castSucc c) * Polynomial.aeval w₀ U =
    algebraMap L₀ S₀ (aeval (transverseSourceCoordinate K) c) * Polynomial.aeval w₀ U
  rw [transverseSourceCoordinate_aeval_source_value]

/-- A transverse source polynomial has no derivative in the original
vertex coordinate. -/
theorem transverse_rename_vertex_derivative_zero (c : A₀) :
    pderiv (Fin.last 3) (rename Fin.castSucc c) = 0 := by
  induction c using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_zero]
  | mul_X P i hP =>
      rw [map_mul, rename_X, pderiv_mul, hP, pderiv_X]
      simp only [Pi.single_eq_of_ne (Fin.castSucc_ne_last i), zero_mul, mul_zero, add_zero]

variable [CharZero K]

/-- Every transverse source polynomial has vertex degree zero. -/
theorem transverse_rename_vertex_degree_zero (c : A₀) :
    (rename Fin.castSucc c).degreeOf (Fin.last 3) = 0 :=
  degreeOf_eq_zero_of_pderiv_eq_zero _ _ (transverse_rename_vertex_derivative_zero c)

end DimensionFourDependence
