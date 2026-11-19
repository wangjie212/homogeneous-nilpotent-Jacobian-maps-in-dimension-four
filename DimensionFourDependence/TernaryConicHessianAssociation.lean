import DimensionFourDependence.TernaryConicWitness
import DimensionFourDependence.QuadraticHessianLinearTransport
import DimensionFourDependence.FiberBoundaryCoefficientExtension
import DimensionFourDependence.QuadraticFiberLeadingBinaryValue

/-! # The original conic Hessian in a transverse new chart -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u v
set_option maxHeartbeats 2100000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "Out₂" => (ternaryRationalOutputPair (K := K))
local notation "Coeff" => (coefficientField (K := K))

theorem TernaryConicWitness.leading_equation {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H) :
    homogeneousComponent 2 W.equation = C ((2 : (Coeff (Out₂ H)))⁻¹) * quadraticFormPolynomial W.hessian :=
  quadraticFiberPolynomial_leading_component _ _ _

/-- The exact affine relation compares the two symmetric Hessian
polynomials after the induced coefficient-field transport. -/
theorem TernaryConicWitness.hessian_linear_association
    {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H)
    (T S : Matrix (Fin 3) (Fin 3) K) (hTS : T * S = 1) (hST : S * T = 1)
    (V : TernaryConicWitness (K := K) (linearPolynomialConjugate T S H))
    (hA : (W.restrictedFrame S).det ≠ 0) :
    ∃ (α : (Coeff (Out₂ H)) ≃ₐ[K] coefficientField (K := K) (ternaryRationalOutputPair
        (linearPolynomialConjugate T S H))) (c : (Coeff (Out₂ H))), c ≠ 0 ∧
      aeval (linearPolynomialMap (W.restrictedFrame S))
        (quadraticFormPolynomial (V.hessian.map α.symm)) = C c * quadraticFormPolynomial W.hessian := by
  obtain ⟨α, c, hc, h⟩ := ternary_conic_transverse_chart_leading_relation_associated
    T S hTS hST H W.nilpotent W.independent V.independent W.lastOutput W.planeConstant
    W.planeConstant_value W.equation W.relation_irreducible W.relation_degree W.relation_ideal
    V.equation V.equation_vanishes V.relation_degree hA
  have hEq := homogeneous_component_coefficient_map α.symm.toRingHom V.equation 2
  rw [hEq, W.leading_equation, V.leading_equation] at h
  simp only [map_mul, MvPolynomial.map_C, map_inv₀, map_ofNat,
    quadraticFormPolynomial_map_coefficients, aeval_C, algebraMap_eq] at h
  let E := coefficientField (K := K) (ternaryRationalOutputPair H)
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  let k : MvPolynomial (Fin 2) (Coeff (Out₂ H)) := C ((2 : (Coeff (Out₂ H)))⁻¹)
  have hk : k ≠ 0 := C_ne_zero.mpr (inv_ne_zero two_ne_zero)
  refine ⟨α, c, hc, mul_left_cancel₀ hk ?_⟩
  rw [mul_left_comm k (C c)]
  exact h

/-- A root in the old projected chart maps to a root of the pulled-back
Hessian of the new chart under the same linear transition. -/
theorem quadraticFormPolynomial_associated_linear_direction_zero
    {B : Type u} {E : Type v} [Field B] [Field E] [Algebra B E]
    (A U V : Matrix (Fin 2) (Fin 2) B) (c : B)
    (he : aeval (linearPolynomialMap A) (quadraticFormPolynomial V) =
      C c * quadraticFormPolynomial U)
    (e : Fin 2 → E) (hz : aeval e (quadraticFormPolynomial U) = 0) :
    aeval (A.map (algebraMap B E) *ᵥ e) (quadraticFormPolynomial V) = 0 := by
  have h := congrArg (aeval e) he
  change aeval e (linearPolynomialPullback A (quadraticFormPolynomial V)) =
    aeval e (C c * quadraticFormPolynomial U) at h
  rw [linearPolynomialPullback_aeval_extension, map_mul, hz, mul_zero] at h
  exact h

/-- The determinant condition is intrinsic to the leading form of the
conic in any transverse chart. -/
theorem TernaryConicWitness.hessian_det_zero_iff_of_linear_association
    {H : Fin 3 → R₃} (W : TernaryConicWitness (K := K) H) {G : Fin 3 → R₃} (V : TernaryConicWitness (K := K) G)
    (A : Matrix (Fin 2) (Fin 2) (Coeff (Out₂ H))) (hA : A.det ≠ 0)
    (α : (Coeff (Out₂ H)) ≃ₐ[K] coefficientField (K := K) (ternaryRationalOutputPair G))
    (c : (Coeff (Out₂ H))) (hc : c ≠ 0)
    (h : aeval (linearPolynomialMap A) (quadraticFormPolynomial (V.hessian.map α.symm)) =
      C c * quadraticFormPolynomial W.hessian) :
    V.hessian.det = 0 ↔ W.hessian.det = 0 := by
  let E := coefficientField (K := K) (ternaryRationalOutputPair H)
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hs (i j : Fin 2) : (V.hessian.map α.symm) i j = (V.hessian.map α.symm) j i :=
    congrArg α.symm (V.hessian_symmetric i j)
  have he := symmetric_quadratic_form_linear_association_det_zero_iff A W.hessian
    (V.hessian.map α.symm) hA c hc W.hessian_symmetric hs h
  change ((α.symm.toRingHom).mapMatrix V.hessian).det = 0 ↔ _ at he
  rw [← RingHom.map_det, map_eq_zero] at he
  exact he

end DimensionFourDependence
