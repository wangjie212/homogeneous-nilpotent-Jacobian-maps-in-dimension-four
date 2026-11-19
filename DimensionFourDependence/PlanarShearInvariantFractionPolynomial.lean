import DimensionFourDependence.PlanarPrimitiveShearFactor
import DimensionFourDependence.PlanarInvariantPolynomialKernel

/-! # The primitive multiplier is a polynomial in the shear invariant over the fraction field -/

namespace DimensionFourDependence.Shear

open Matrix MvPolynomial

set_option maxHeartbeats 1200000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "L" => FractionRing R₂
local notation "Aₗ" => MvPolynomial (Fin 2) L

noncomputable def activeFractionPolynomialHom : R₄ →+* Aₗ :=
  (MvPolynomial.map (algebraMap R₂ L)).comp planarCoefficientEquiv.toRingHom

theorem activeFractionPolynomialHom_apply (p : R₄) :
    activeFractionPolynomialHom p = activeFractionPolynomial p := rfl

theorem activeFractionPolynomialHom_base4 (a : R₂) :
    activeFractionPolynomialHom (base4 a) = (C (algebraMap R₂ L a) : Aₗ) := by
  rw [activeFractionPolynomialHom_apply]
  simp only [activeFractionPolynomial, planarCoefficientEquiv_base4, MvPolynomial.map_C]

/-- Trace zero gives the constant active derivation annihilating the
actual primitive multiplier, and hence its invariant-variable polynomial. -/
theorem normalized_planar_shear_multiplier_is_polynomial_over_fraction_field
    (A : Fin 2 → R₄) (hN : IsNilpotent (planarActiveJacobian A))
    (a b : R₂) (ha : a ≠ 0) (q : R₄)
    (hx : planarActiveNormalized (A 0) = base4 b * q)
    (hy : planarActiveNormalized (A 1) = -base4 a * q) :
    ∃ f : Polynomial L, activeFractionPolynomial q =
      Polynomial.aeval (C (algebraMap R₂ L a) * X 0 + C (algebraMap R₂ L b) * X 1 : Aₗ) f := by
  let B : Fin 2 → R₄ := fun i => planarActiveNormalized (A i)
  let ψ := activeFractionPolynomialHom (K := K)
  have hnil : IsNilpotent (jac (fun i => ψ (B i))) := by
    change IsNilpotent (jac (fun i => activeFractionPolynomial (planarActiveNormalized (A i))))
    rw [jac_activeFractionPolynomial, planarActiveJacobian_normalized]
    exact hN.map ψ.mapMatrix
  have htrace := (isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have htr : pderiv 0 (ψ (B 0)) + pderiv 1 (ψ (B 1)) = 0 := by
    simpa only [trace, diag, Fin.sum_univ_two, jac, Matrix.of_apply] using htrace
  have hbase (p : R₂) : ψ (base4 p) = C (algebraMap R₂ L p) := activeFractionPolynomialHom_base4 p
  change pderiv 0 (ψ (planarActiveNormalized (A 0))) +
    pderiv 1 (ψ (planarActiveNormalized (A 1))) = 0 at htr
  rw [hx, hy, ψ.map_mul, ψ.map_mul, ψ.map_neg, hbase, hbase] at htr
  have hD : C (algebraMap R₂ L b) * pderiv 0 (ψ q) - C (algebraMap R₂ L a) * pderiv 1 (ψ q) = 0 := by
    simp only [pderiv_mul, pderiv_C, zero_mul, zero_add, map_neg, neg_zero, neg_mul] at htr
    linear_combination htr
  exact planar_constant_direction_kernel_is_polynomial_in_invariant _ _
    (by simpa only [map_zero] using (IsFractionRing.injective R₂ L).ne ha) _ hD

end DimensionFourDependence.Shear
