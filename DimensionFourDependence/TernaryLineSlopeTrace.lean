import DimensionFourDependence.TernaryConstantRightKernelDependence
import DimensionFourDependence.ClosedFieldCoefficientPartials

/-! # A ternary invariant line with slope in the fixed coordinate is impossible -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 1800000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "∂" => (rationalPartial (K := K) (n := 3))

/-- The derivation of an invariant line with first coordinate fixed,
third coordinate as parameter and second-coordinate slope `s`. -/
noncomputable def ternaryLineSlopeDerivation (s : F) : Derivation K F F :=
  s • ∂ 1 + ∂ 2

/-- Commuting the invariant direction with a source partial introduces
exactly the derivative of its slope. -/
theorem ternaryLineSlopeDerivation_commute_partial (s f : F) (j : Fin 3) :
    ternaryLineSlopeDerivation s (∂ j f) =
      ∂ j (ternaryLineSlopeDerivation s f) - ∂ j s * ∂ 1 f := by
  simp only [ternaryLineSlopeDerivation, Derivation.add_apply, Derivation.smul_apply,
    smul_eq_mul, map_add, Derivation.leibniz, rationalPartials_commute j 1 f,
    rationalPartials_commute j 2 f]
  ring

/-- Applying the line derivation to the original nilpotent trace
identity eliminates all invariant terms except the variable slope term. -/
theorem invariant_ternary_line_trace_slope_identity
    (H : Fin 3 → R₃) (hN : IsNilpotent (jac H)) (s : F)
    (hD : ∀ i, ternaryLineSlopeDerivation s (ι (H i)) = 0)
    (hy : ∂ 1 s = 0) (hz : ∂ 2 s = 0) :
    ∂ 0 s * ∂ 1 (ι (H 0)) = 0 := by
  have htrace : pderiv 0 (H 0) + pderiv 1 (H 1) + pderiv 2 (H 2) = 0 := by
    simpa only [Matrix.trace, Matrix.diag, jac, Matrix.of_apply, Fin.sum_univ_three] using
      (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  have he : ∂ 0 (ι (H 0)) + ∂ 1 (ι (H 1)) + ∂ 2 (ι (H 2)) = 0 := by
    rw [rationalPartial_polynomial, rationalPartial_polynomial, rationalPartial_polynomial,
      ← map_add, ← map_add, htrace, map_zero]
  have hd := congrArg (ternaryLineSlopeDerivation s) he
  change ternaryLineSlopeDerivation s (∂ 0 (ι (H 0)) + ∂ 1 (ι (H 1)) + ∂ 2 (ι (H 2))) =
    ternaryLineSlopeDerivation s 0 at hd
  simp only [map_add, map_zero, ternaryLineSlopeDerivation_commute_partial, hD, hy, hz,
    zero_mul, sub_zero, add_zero, zero_sub, neg_eq_zero] at hd
  exact hd

/-- A normalized component depending only on its own source
coordinate is zero when the original Jacobian is nilpotent. -/
theorem normalized_nilpotent_ternary_single_coordinate_component_eq_zero
    (H : Fin 3 → R₃) (hN : IsNilpotent (jac H))
    (h0 : aeval (fun _ : Fin 3 => (0 : K)) (H 0) = 0)
    (hy : pderiv 1 (H 0) = 0) (hz : pderiv 2 (H 0) = 0) :
    H 0 = 0 := by
  let v : Fin 3 → R₃ := Pi.single 0 1
  have hv : v ≠ 0 := by
    intro he
    have hi := congrFun he (0 : Fin 3)
    simp [v] at hi
  have he : v ᵥ* jac H = pderiv 0 (H 0) • v := by
    rw [show v = Pi.single 0 1 from rfl, Matrix.single_one_vecMul]
    funext i
    fin_cases i <;> simp [jac, Pi.single_apply, hy, hz]
  have hx := eigenvalue_zero_of_nilpotent (jac H) hN v hv (pderiv 0 (H 0)) he
  apply normalized_polynomial_eq_zero_of_partials_zero (H 0) h0
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · exact hz

variable [IsAlgClosed K]

/-- If the slope's moving-coordinate partials vanish, the invariant
line and the original trace force a constant component relation. -/
theorem invariant_ternary_line_with_fixed_coordinate_slope_componentsDependent
    (H : Fin 3 → R₃) (h0 : ∀ i, aeval (fun _ : Fin 3 => (0 : K)) (H i) = 0)
    (hN : IsNilpotent (jac H)) (s : F)
    (hD : ∀ i, ternaryLineSlopeDerivation s (ι (H i)) = 0)
    (hy : ∂ 1 s = 0) (hz : ∂ 2 s = 0) :
    ComponentsDependent H := by
  by_cases hx : ∂ 0 s = 0
  · obtain ⟨a, ha⟩ := closed_field_all_rational_partials_zero_is_scalar s (by
      intro j
      fin_cases j
      · exact hx
      · exact hy
      · exact hz)
    let c : Fin 3 → K := ![0,a,1]
    have hc : c ≠ 0 := by
      intro he
      exact one_ne_zero (congrFun he (2 : Fin 3))
    apply normalized_ternary_nilpotent_constant_right_kernel_componentsDependent H h0 hN c hc
    funext i
    simp only [mulVec, dotProduct, jac, Matrix.of_apply, Fin.sum_univ_three]
    change pderiv 0 (H i) * C 0 + pderiv 1 (H i) * C a + pderiv 2 (H i) * C 1 = 0
    simp only [map_zero, map_one, mul_zero, mul_one, zero_add]
    apply IsFractionRing.injective R₃ F
    have h := hD i
    change s * ∂ 1 (ι (H i)) + ∂ 2 (ι (H i)) = 0 at h
    simpa only [map_add, map_mul, map_zero, ← algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K R₃ F, ← ha, ← rationalPartial_polynomial,
      mul_comm] using h
  · have hp : ∂ 1 (ι (H 0)) = 0 := (mul_eq_zero.mp
      (invariant_ternary_line_trace_slope_identity H hN s hD hy hz)).resolve_left hx
    have hz₀ : ∂ 2 (ι (H 0)) = 0 := by
      have he := hD 0
      change s * ∂ 1 (ι (H 0)) + ∂ 2 (ι (H 0)) = 0 at he
      simpa only [hp, mul_zero, zero_add] using he
    have hP (j : Fin 3) (hj : ∂ j (ι (H 0)) = 0) : pderiv j (H 0) = 0 := by
      apply IsFractionRing.injective R₃ F
      simpa only [rationalPartial_polynomial, map_zero] using hj
    have hzero := normalized_nilpotent_ternary_single_coordinate_component_eq_zero
      H hN (h0 0) (hP 1 hp) (hP 2 hz₀)
    refine ⟨![1,0,0], ?_, ?_⟩
    · intro he
      exact one_ne_zero (congrFun he (0 : Fin 3))
    · simp [Fin.sum_univ_three, hzero]

end DimensionFourDependence
