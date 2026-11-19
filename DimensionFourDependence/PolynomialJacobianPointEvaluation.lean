import DimensionFourDependence.LinearPolynomialConjugacy
import DimensionFourDependence.NonconstantRatioSpecialization

/-! # Exact source-point evaluation of Jacobian iterates and linear conjugacy -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] {n : ℕ}

/-- Evaluating the actual squared-Jacobian source vector is exactly
the second iterate of the evaluated original Jacobian on that point. -/
theorem polynomial_jacobian_second_euler_iterate_point_value
    (H : Fin n → MvPolynomial (Fin n) K) (x : Fin n → K) :
    (fun i => aeval x ((jac H ^ 2 *ᵥ coordVec) i)) =
      ((jac H).map (aeval x)) ^ 2 *ᵥ x := by
  have hpow : (jac H ^ 2).map (aeval x) = ((jac H).map (aeval x)) ^ 2 :=
    Matrix.map_pow (jac H) (aeval x).toRingHom 2
  rw [← hpow]
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul,
    coordVec, aeval_X]

/-- A nonzero second polynomial iterate supplies an actual source
point over the original infinite coefficient field where it remains
nonzero. No generic point or exceptional-set hypothesis is supplied. -/
theorem nonzero_second_polynomial_jacobian_iterate_constructs_source_point
    [Infinite K] (H : Fin n → MvPolynomial (Fin n) K)
    (hW : jac H ^ 2 *ᵥ coordVec ≠ 0) :
    ∃ x : Fin n → K, ((jac H).map (aeval x)) ^ 2 *ᵥ x ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, (jac H ^ 2 *ᵥ coordVec) i ≠ 0 := by
    simpa only [ne_eq, _root_.funext_iff, Pi.zero_apply, not_forall] using hW
  obtain ⟨x, hx⟩ := polynomial_exists_source_value_ne_zero _ hi
  refine ⟨x, ?_⟩
  intro hz
  have he := congrFun ((polynomial_jacobian_second_euler_iterate_point_value H x).trans hz) i
  exact hx (by simpa only [Pi.zero_apply, aeval_eq_eval] using he)

/-- The Jacobian at every transformed point is the literal similarity
of the original evaluated Jacobian at the corresponding source point. -/
theorem linear_polynomial_conjugate_jacobian_point_value
    (T S : Matrix (Fin n) (Fin n) K) (H : Fin n → MvPolynomial (Fin n) K)
    (x : Fin n → K) :
    (jac (linearPolynomialConjugate T S H)).map (aeval x) =
      S * (jac H).map (aeval (T *ᵥ x)) * T := by
  have hS : (S.map MvPolynomial.C).map (aeval x) = S := by
    funext i j
    simp only [Matrix.map_apply, aeval_C, algebraMap_eq, Algebra.algebraMap_self, RingHom.id_apply]
  have hT : (T.map MvPolynomial.C).map (aeval x) = T := by
    funext i j
    simp only [Matrix.map_apply, aeval_C, algebraMap_eq, Algebra.algebraMap_self, RingHom.id_apply]
  have hmid : ((jac H).map (aeval (linearPolynomialMap T))).map (aeval x) =
      (jac H).map (aeval (T *ᵥ x)) := by
    funext i j
    exact linearPolynomialPullback_aeval T ((jac H) i j) x
  rw [jac_linearPolynomialConjugate]
  change (S.map MvPolynomial.C * (jac H).map (aeval (linearPolynomialMap T)) *
    T.map MvPolynomial.C).map (aeval x).toRingHom = _
  rw [Matrix.map_mul, Matrix.map_mul]
  change (S.map MvPolynomial.C).map (aeval x) *
    ((jac H).map (aeval (linearPolynomialMap T))).map (aeval x) *
    (T.map MvPolynomial.C).map (aeval x) = _
  rw [hS, hT, hmid]

end DimensionFourDependence
