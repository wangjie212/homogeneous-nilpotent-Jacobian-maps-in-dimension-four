import DimensionFourDependence.QuadraticConeLevelSubstitution
import DimensionFourDependence.QuadraticEulerComparison
import DimensionFourDependence.NilpotentConstantConeCoordinate

/-! # The quadratic trace comparison and its original nilpotent obstruction

The degree-two transverse component of (4.11) is A₂'(t)Q₂.
The other terms vanish in that component. A nonzero original Q₂ remains
nonzero over K[t], forcing A₂'=0, and hence component dependence for the
original homogeneous nilpotent map once P=w-Q has been established.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

/-- The exact transverse quadratic component of the entire (4.11). -/
theorem quadratic_cone_level_trace_quadratic_component
    (d : ℕ) (Q : MvPolynomial (Fin 2) K) (hQ : Q.totalDegree ≤ 2)
    (A B : Fin 3 → Polynomial K) :
    homogeneousComponent 2 (quadraticConeLevelTracePolynomial d Q A B) =
      C (A 1).derivative * homogeneousComponent 2 (MvPolynomial.map Polynomial.C Q) := by
  let U := MvPolynomial.map Polynomial.C Q
  have hU : U.totalDegree ≤ 2 :=
    (Finset.sup_mono (support_map_subset Polynomial.C Q)).trans hQ
  have hconst (p : Polynomial K) : homogeneousComponent 2 (C p : MvPolynomial (Fin 2) (Polynomial K)) = 0 :=
    homogeneousComponent_eq_zero 2 _ (by simp)
  have hlin (i : Fin 2) : homogeneousComponent 2 (X i : MvPolynomial (Fin 2) (Polynomial K)) = 0 :=
    homogeneousComponent_eq_zero 2 _ (by simp)
  have hpart (i : Fin 2) : homogeneousComponent 2 (pderiv i U) = 0 :=
    homogeneousComponent_eq_zero 2 _ (by
      have he := quadratic_polynomial_partial_degree_le_one U hU i
      omega)
  have heuler : homogeneousComponent 2 (X 0 * pderiv 0 U + X 1 * pderiv 1 U - U) =
      homogeneousComponent 2 U := by
    simpa [Fin.sum_univ_succ] using quadratic_component_euler_sub_self U
  dsimp only [U] at hpart heuler
  simp only [map_add, map_sub] at heuler
  simp only [quadraticConeLevelTracePolynomial, map_add, map_sub,
    homogeneousComponent_C_mul, hconst, hlin, hpart, heuler,
    mul_zero, zero_add, add_zero, sub_zero]

/-- The original nonzero quadratic part forces the second scalar
polynomial derivative zero from the complete level trace identity. -/
theorem quadratic_cone_level_trace_forces_second_scalar_derivative_zero
    (d : ℕ) (Q : MvPolynomial (Fin 2) K) (hQ : Q.totalDegree ≤ 2)
    (hQ₂ : homogeneousComponent 2 Q ≠ 0) (A B : Fin 3 → Polynomial K)
    (htrace : quadraticConeLevelTracePolynomial d Q A B = 0) :
    (A 1).derivative = 0 := by
  have hcomponent : C (A 1).derivative * homogeneousComponent 2 (MvPolynomial.map Polynomial.C Q) = 0 := by
    rw [← quadratic_cone_level_trace_quadratic_component d Q hQ A B, htrace, map_zero]
  have hQ₂' : homogeneousComponent 2 (MvPolynomial.map Polynomial.C Q) ≠ 0 := by
    rw [homogeneous_component_coefficient_map]
    simpa only [map_zero] using
      (MvPolynomial.map_injective Polynomial.C Polynomial.C_injective).ne hQ₂
  have hc : C (A 1).derivative = (0 : MvPolynomial (Fin 2) (Polynomial K)) :=
    (mul_eq_zero.mp hcomponent).resolve_right hQ₂'
  apply MvPolynomial.C_injective (Fin 2) (Polynomial K)
  simpa only [map_zero] using hc

/-- The actual original affine trace with P=w-Q forces A₂'=0, by
transporting the whole identity to independent transverse level variables. -/
theorem quadratic_parameter_affine_trace_forces_second_scalar_derivative_zero
    (d : ℕ) (Q : MvPolynomial (Fin 2) K) (hQ : Q.totalDegree ≤ 2)
    (hQ₂ : homogeneousComponent 2 Q ≠ 0) (A B : Fin 3 → Polynomial K)
    (htrace : affineConeTracePolynomial d (X 2 - rename Fin.castSucc Q) A B = 0) :
    (A 1).derivative = 0 := by
  apply quadratic_cone_level_trace_forces_second_scalar_derivative_zero d Q hQ hQ₂ A B
  rw [← affine_cone_trace_transports_to_quadratic_level_identity, htrace, map_zero]

variable [CharZero K]

/-- With the quadratic affine parameter identified, the original
homogeneous nilpotent map has zero second component and dependent
components. This is the complete final algebraic trace exclusion. -/
theorem nilpotent_quadratic_parameter_cone_forms_force_dependence
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (Q : MvPolynomial (Fin 2) K) (hQ : Q.totalDegree ≤ 2)
    (hQ₂ : homogeneousComponent 2 Q ≠ 0) (A B : Fin 3 → Polynomial K)
    (hfirst : ∀ i : Fin 3, secondCoordinateAffineChart (H i.castSucc) =
      Polynomial.aeval (X 2 - rename Fin.castSucc Q) (A i))
    (hlast : secondCoordinateAffineChart (H (Fin.last 3)) =
      Polynomial.aeval (X 2 - rename Fin.castSucc Q) (B 0) * X 0 +
        Polynomial.aeval (X 2 - rename Fin.castSucc Q) (B 1) +
          Polynomial.aeval (X 2 - rename Fin.castSucc Q) (B 2) * X 1) :
    H 1 = 0 ∧ ComponentsDependent H := by
  have htrace := nilpotent_cone_affine_polynomial_forms_trace_zero H hH hN _ A B hfirst hlast
  have hder := quadratic_parameter_affine_trace_forces_second_scalar_derivative_zero d Q hQ hQ₂ A B htrace
  have hA := Polynomial.eq_C_of_derivative_eq_zero hder
  have hsecond : secondCoordinateAffineChart (H 1) =
      Polynomial.aeval (X 2 - rename Fin.castSucc Q) (A 1) := by
    simpa only [show (1 : Fin 3).castSucc = (1 : Fin 4) by decide] using hfirst 1
  have hc : secondCoordinateAffineChart (H 1) = C ((A 1).coeff 0) := by
    rw [hsecond]
    conv_lhs => rw [hA]
    rw [Polynomial.aeval_C]
    rfl
  exact nilpotent_constant_second_chart_coordinate_forces_dependence H hd hH hN _ hc

/-- The final exclusion also allows every affine rescaling of the
quadratic parameter. Polynomial composition constructs the transformed
scalar families internally. -/
theorem nilpotent_affinely_rescaled_quadratic_parameter_cone_forms_force_dependence
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d)
    (hH : IsHomogMap H d) (hN : IsNilpotent (jac H))
    (P : MvPolynomial (Fin 3) K) (a b : K)
    (Q : MvPolynomial (Fin 2) K) (hQ : Q.totalDegree ≤ 2)
    (hQ₂ : homogeneousComponent 2 Q ≠ 0)
    (hP : P = C a * (X 2 - rename Fin.castSucc Q) + C b)
    (A B : Fin 3 → Polynomial K)
    (hfirst : ∀ i : Fin 3, secondCoordinateAffineChart (H i.castSucc) = Polynomial.aeval P (A i))
    (hlast : secondCoordinateAffineChart (H (Fin.last 3)) =
      Polynomial.aeval P (B 0) * X 0 + Polynomial.aeval P (B 1) + Polynomial.aeval P (B 2) * X 1) :
    H 1 = 0 ∧ ComponentsDependent H := by
  let φ : Polynomial K := Polynomial.C a * Polynomial.X + Polynomial.C b
  have hcomp (F : Polynomial K) :
      Polynomial.aeval (X 2 - rename Fin.castSucc Q) (F.comp φ) = Polynomial.aeval P F := by
    rw [Polynomial.aeval_comp]
    have he : Polynomial.aeval (X 2 - rename Fin.castSucc Q) φ = P := by
      rw [hP]
      simp only [φ, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      rfl
    rw [he]
  apply nilpotent_quadratic_parameter_cone_forms_force_dependence H hd hH hN Q hQ hQ₂
    (fun i => (A i).comp φ) (fun i => (B i).comp φ)
  · intro i
    rw [hcomp]
    exact hfirst i
  · simp only [hcomp]
    exact hlast

end DimensionFourDependence
