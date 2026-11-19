import DimensionFourDependence.ParametricGraphCubic

/-! # The zero acceleration equation D_b²(nc)=0 in (4.3)

Directions algebraic over the ruling parameter are constant for their own
directional derivation. The original modified-quadric equation then gives
the zero second derivative of n times the first invariant.
-/

namespace DimensionFourDependence

open Matrix

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

theorem coordinate_direction_coordinate (δ : Fin n → Derivation K F F)
    (y v : Fin n → F) (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0) (j : Fin n) :
    coordinateEuler v δ (y j) = v j := by
  rw [coordinateEuler_apply]
  simp [hcoord, apply_ite]

theorem coordinate_direction_apply_eq_gradient_pairing
    (δ : Fin n → Derivation K F F) (v : Fin n → F) (c : F) :
    coordinateEuler v δ c = (fun i => δ i c) ⬝ᵥ v := by
  simp only [coordinateEuler_apply, dotProduct, mul_comm]

/-- A constant direction's actual second derivative is the Hessian
self-pairing, retaining the original coordinate derivative order. -/
theorem coordinate_direction_second_derivative
    (δ : Fin n → Derivation K F F) (v : Fin n → F)
    (hv : ∀ i, coordinateEuler v δ (v i) = 0) (c : F) :
    coordinateEuler v δ (coordinateEuler v δ c) = matrixBilinearPairing (derivationHessian δ c) v v := by
  rw [coordinateEuler_apply v δ c, map_sum]
  simp only [Derivation.leibniz, hv, smul_eq_mul, mul_zero, add_zero,
    coordinateEuler_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [matrixBilinearPairing, derivationHessian, of_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable (f : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => f (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => f (rationalParameterDerivative K (A i))) ≠ 0)

local notation "a" => fun i => f (rationalParameterDerivative K (A i))
local notation "b" => fun i => f (rationalParameterDerivative K (rationalParameterDerivative K (A i)))
local notation "N" => parametricRulingDenominator f A y

include hcoord htangent hfirst

/-- Every vector in the actual ruling kills the actual parameter. -/
theorem parametric_ruling_direction_fixes_parameter (v : Fin n → F) (hv : (a) ⬝ᵥ v = 0) :
    coordinateEuler v δ (f RatFunc.X) = 0 := by
  rw [coordinateEuler_apply]
  simp only [parametric_ruling_parameter_partial f δ y hcoord A htangent hfirst]
  have he : (∑ i, v i * (-(a) i / (N))) = -((a) ⬝ᵥ v) / (N) := by
    simp only [dotProduct, div_eq_mul_inv, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, hv, neg_zero, zero_div]

/-- Along a ruling direction the denominator derivative is A'' dot b. -/
theorem parametric_ruling_direction_denominator_derivative (v : Fin n → F) (hv : (a) ⬝ᵥ v = 0) :
    coordinateEuler v δ (N) = (b) ⬝ᵥ v := by
  have ht := parametric_ruling_direction_fixes_parameter f δ y hcoord A htangent hfirst v hv
  have hzero (r : RatFunc K) : coordinateEuler v δ (f r) = 0 := by
    rw [rational_parameter_chain_rule f (coordinateEuler v δ) r, ht, mul_zero]
  unfold parametricRulingDenominator
  rw [derivation_dotProduct]
  simp [dotProduct, hzero, coordinate_direction_coordinate δ y v hcoord]

omit δ y hcoord A htangent hfirst in
/-- A derivation fixing the rational parameter annihilates every
coefficient algebraic over its actual parameter field. -/
theorem parameter_algebraic_coefficient_direction_constant [CharZero K]
    (D : Derivation K F F) (ht : D (f RatFunc.X) = 0) (x : F)
    (hx : IsAlgebraic f.fieldRange x) : D x = 0 := by
  let M := f.fieldRange
  let : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  have hM : M ≤ derivationConstants D := by
    rintro _ ⟨r, rfl⟩
    change D (f r) = 0
    rw [rational_parameter_chain_rule f D r, ht, mul_zero]
  exact derivation_zero_of_isAlgebraic (derivationOverConstantSubfield D M hM) x hx

variable [CharZero K]

/-- A direction defined over an algebraic extension of the ruling
parameter is constant for the actual directional derivative. The
modified quadratic equation therefore gives D_b²(nc)=0, the second
equation of (4.3), without assuming that acceleration separately. -/
theorem parametric_ruling_zero_acceleration_of_modified_boundary
    (v : Fin n → F) (hv : (a) ⬝ᵥ v = 0)
    (halg : ∀ i, IsAlgebraic f.fieldRange (v i)) (c : F)
    (hboundary : matrixBilinearPairing (derivationHessian δ c) v v -
      (2 / 3 : F) * (parametricGraphCubicCovector f A y ⬝ᵥ v) * ((fun i => δ i c) ⬝ᵥ v) = 0) :
    coordinateEuler v δ (coordinateEuler v δ ((N) * c)) = 0 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let D := coordinateEuler v δ
  have ht : D (f RatFunc.X) = 0 :=
    parametric_ruling_direction_fixes_parameter f δ y hcoord A htangent hfirst v hv
  have hzero (r : RatFunc K) : D (f r) = 0 := by
    rw [rational_parameter_chain_rule f D r, ht, mul_zero]
  have hvD (i : Fin n) : D (v i) = 0 :=
    parameter_algebraic_coefficient_direction_constant f D ht (v i) (halg i)
  have hnD : D (N) = (b) ⬝ᵥ v :=
    parametric_ruling_direction_denominator_derivative f δ y hcoord A htangent hfirst v hv
  have hnDD : D (D (N)) = 0 := by
    rw [hnD, derivation_dotProduct]
    simp [dotProduct, hzero, hvD]
  have hcDD : D (D c) = matrixBilinearPairing (derivationHessian δ c) v v :=
    coordinate_direction_second_derivative δ v hvD c
  have hcD : D c = (fun i => δ i c) ⬝ᵥ v := coordinate_direction_apply_eq_gradient_pairing δ v c
  rw [← hcDD, ← hcD, parametric_graph_cubic_covector_on_ruling f y A v hv] at hboundary
  have hprod : D (D ((N) * c)) = (N) * D (D c) + 2 * ((b) ⬝ᵥ v) * D c := by
    rw [D.leibniz]
    simp only [smul_eq_mul, map_add, D.leibniz]
    rw [hnDD]
    simp only [mul_zero]
    rw [hnD]
    ring
  change D (D ((N) * c)) = 0
  rw [hprod]
  have hN := parametric_ruling_denominator_ne_zero f δ y hcoord A htangent hfirst
  have he : (D (D c) - (2 / 3 : F) * (-3 * ((b) ⬝ᵥ v) / (N)) * D c) * (N) =
      (N) * D (D c) + 2 * ((b) ⬝ᵥ v) * D c := by
    field_simp
    ring
  rw [hboundary, zero_mul] at he
  exact he.symm

end DimensionFourDependence
