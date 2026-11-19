import DimensionFourDependence.ParametricGraphHessian
import DimensionFourDependence.SymmetrizedCubicFactor

/-! # The actual rational-parameter cubic factor and its value on the ruling -/

namespace DimensionFourDependence

open Matrix

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- The explicit linear factor of the third graph derivative. -/
noncomputable def parametricGraphCubicCovector
    (f : RatFunc K →ₐ[K] F) (A : Fin n → RatFunc K) (y : Fin n → F) (i : Fin n) : F :=
  ((fun j => f (rationalParameterDerivative K (rationalParameterDerivative K
    (rationalParameterDerivative K (A j))))) ⬝ᵥ y) *
      f (rationalParameterDerivative K (A i)) / (parametricRulingDenominator f A y) ^ 2 -
        3 * f (rationalParameterDerivative K (rationalParameterDerivative K (A i))) /
          parametricRulingDenominator f A y

variable (f : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => f (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => f (rationalParameterDerivative K (A i))) ≠ 0)
    (h : F) (hgradient : ∀ i, δ i h = f (A i))

local notation "a" => fun i => f (rationalParameterDerivative K (A i))
local notation "b" => fun i => f (rationalParameterDerivative K (rationalParameterDerivative K (A i)))
local notation "c" => (fun i => f (rationalParameterDerivative K (rationalParameterDerivative K
  (rationalParameterDerivative K (A i))))) ⬝ᵥ y
local notation "N" => parametricRulingDenominator f A y

include hcoord htangent hfirst hgradient

/-- Differentiating the constructed Hessian gives the complete third
tensor, including the derivative of its ruling denominator. -/
theorem parametric_graph_cubic_tensor_formula (i j k : Fin n) :
    derivationCubicTensor δ h i j k =
      ((b) i * (a) j * (a) k + (a) i * (b) j * (a) k + (a) i * (a) j * (b) k) / (N) ^ 2 -
        (c) * (a) i * (a) j * (a) k / (N) ^ 3 := by
  have hN := parametric_ruling_denominator_ne_zero f δ y hcoord A htangent hfirst
  change δ i (derivationHessian δ h j k) = _
  rw [parametric_graph_hessian_formula f δ y hcoord A htangent hfirst h hgradient]
  rw [(δ i).leibniz_div, map_neg, (δ i).leibniz,
    rational_parameter_chain_rule f (δ i) (rationalParameterDerivative K (A j)),
    rational_parameter_chain_rule f (δ i) (rationalParameterDerivative K (A k))]
  simp only [parametric_ruling_parameter_partial f δ y hcoord A htangent hfirst,
    parametric_ruling_denominator_partial f δ y hcoord A htangent hfirst, smul_eq_mul]
  field_simp
  ring

/-- The constructed tensor is the symmetric polarization of its
actual linear factor and actual Hessian. -/
theorem parametric_graph_cubic_tensor_polarization (i j k : Fin n) :
    (3 : F) * derivationCubicTensor δ h i j k =
      parametricGraphCubicCovector f A y i * derivationHessian δ h j k +
      parametricGraphCubicCovector f A y j * derivationHessian δ h i k +
      parametricGraphCubicCovector f A y k * derivationHessian δ h i j := by
  rw [parametric_graph_cubic_tensor_formula f δ y hcoord A htangent hfirst h hgradient]
  simp only [parametric_graph_hessian_formula f δ y hcoord A htangent hfirst h hgradient,
    parametricGraphCubicCovector]
  ring

omit δ hcoord htangent hfirst h hgradient in
/-- On the ruling the constructed factor is exactly -3 A''(b)/n,
the coefficient identity (4.2). -/
theorem parametric_graph_cubic_covector_on_ruling (v : Fin n → F)
    (hv : (a) ⬝ᵥ v = 0) :
    parametricGraphCubicCovector f A y ⬝ᵥ v = -3 * ((b) ⬝ᵥ v) / (N) := by
  have he : parametricGraphCubicCovector f A y ⬝ᵥ v =
      (c) * ((a) ⬝ᵥ v) / (N) ^ 2 - 3 * ((b) ⬝ᵥ v) / (N) := by
    simp only [parametricGraphCubicCovector, dotProduct, sub_mul, Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.sum_div]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  rw [he, hv]
  ring

variable [CharZero F]

/-- The original graph cubic polynomial factors by the original
Hessian polynomial. Its linear factor is constructed from the actual
parameter derivatives, rather than assumed as a cubic factor. -/
theorem parametric_graph_cubic_polynomial_factorization :
    cubicFormPolynomial (derivationCubicTensor δ h) =
      linearFormPolynomial (parametricGraphCubicCovector f A y) *
        quadraticFormPolynomial (derivationHessian δ h) :=
  cubicFormPolynomial_eq_linear_mul_quadratic_of_polarization _ _ _
    (parametric_graph_cubic_tensor_polarization f δ y hcoord A htangent hfirst h hgradient)

end DimensionFourDependence
