import DimensionFourDependence.ClosedGaussCoefficientRealization
import DimensionFourDependence.RulingDirectionAcceleration
import DimensionFourDependence.ModifiedCubicFiberBoundary

/-! # Equations (4.1)--(4.2) constructed from the original homogeneous map -/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hGauss : gaussImageDimension H I = 1)

local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
  (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "δ₀" => coefficientPartial (Y) hY
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (y₀)
local notation "Λ₀" => parametricGraphCubicCovector (f₀) (A₀) (y₀)

include hh hGauss

/-- The actual Gauss-dimension-one hypothesis makes the derivative
of the constructed actual graph-gradient nonzero. -/
theorem actual_closed_gauss_graph_gradient_derivative_ne_zero :
    (fun i => (f₀) (rationalParameterDerivative K ((A₀) i))) ≠ 0 := by
  apply parametric_graph_gradient_derivative_ne_zero (f₀) (δ₀) (A₀) h
    (fun i => (closedGaussCoefficientGraphSlope_value H I p hY h hh e i).symm)
  intro hz
  have hr := I.gauss_image_dimension_eq_hessian H p hY h hh
  change derivationHessian (δ₀) h = 0 at hz
  change gaussImageDimension H I = (derivationHessian (δ₀) h).rank at hr
  rw [hz, Matrix.rank_zero, hGauss] at hr
  exact one_ne_zero hr

variable {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)

include hd hH

omit hGauss in
/-- Euler's identity and the constructed nonzero parameter partial
derive the actual graph ruling relation A'(t) dot Y=0. -/
theorem actual_closed_gauss_graph_ruling_equation :
    (fun i => (f₀) (rationalParameterDerivative K ((A₀) i))) ⬝ᵥ (y₀) = 0 :=
  parametric_graph_ruling_equation_of_euler (f₀) (δ₀) (y₀)
    (coefficientPartial_coordinate (Y) hY) (A₀) h
    (fun i => (closedGaussCoefficientGraphSlope_value H I p hY h hh e i).symm)
    (homogeneous_last_output_euler H hd hH p hY h hh)
    (closedGaussCoefficientParameterHom_partial_ne_zero H I p hY h hh e)

/-- The actual denominator n=A''(t) dot Y is nonzero, constructed
from the original homogeneous map without a denominator hypothesis. -/
theorem actual_closed_gauss_graph_denominator_ne_zero : (n₀) ≠ 0 :=
  parametric_ruling_denominator_ne_zero (f₀) (δ₀) (y₀)
    (coefficientPartial_coordinate (Y) hY) (A₀)
    (actual_closed_gauss_graph_ruling_equation H I p hY h hh e hd hH)
    (actual_closed_gauss_graph_gradient_derivative_ne_zero H I p hY h hh e hGauss)

/-- The full actual coefficient Hessian formula in (4.1), derived
from the original map and its constructed actual closed Gauss parameter. -/
theorem actual_closed_gauss_graph_hessian_formula (i j : Fin 3) :
    coefficientHessian (Y) hY h i j =
      -((f₀) (rationalParameterDerivative K ((A₀) i)) *
        (f₀) (rationalParameterDerivative K ((A₀) j))) / (n₀) :=
  parametric_graph_hessian_formula (f₀) (δ₀) (y₀)
    (coefficientPartial_coordinate (Y) hY) (A₀)
    (actual_closed_gauss_graph_ruling_equation H I p hY h hh e hd hH)
    (actual_closed_gauss_graph_gradient_derivative_ne_zero H I p hY h hh e hGauss)
    h (fun i => (closedGaussCoefficientGraphSlope_value H I p hY h hh e i).symm) i j

/-- The original actual cubic coefficient polynomial factors by
the original actual Hessian polynomial with a constructed linear factor. -/
theorem actual_closed_gauss_graph_cubic_polynomial_factorization :
    cubicFormPolynomial (coefficientCubicTensor (Y) hY h) =
      linearFormPolynomial (Λ₀) * quadraticFormPolynomial (coefficientHessian (Y) hY h) := by
  let : CharZero (L) := charZero_of_injective_algebraMap (algebraMap K (L)).injective
  exact parametric_graph_cubic_polynomial_factorization (f₀) (δ₀) (y₀)
    (coefficientPartial_coordinate (Y) hY) (A₀)
    (actual_closed_gauss_graph_ruling_equation H I p hY h hh e hd hH)
    (actual_closed_gauss_graph_gradient_derivative_ne_zero H I p hY h hh e hGauss)
    h (fun i => (closedGaussCoefficientGraphSlope_value H I p hY h hh e i).symm)

omit hGauss in
/-- The actual closed Gauss parameter has output Euler weight zero,
deduced from its original homogeneous source realization. -/
theorem actual_closed_gauss_graph_parameter_output_euler_zero :
    coefficientEuler (Y) hY ((f₀) RatFunc.X) = 0 := by
  have hsource : sourceEuler (K := K) ((f₀) RatFunc.X : FractionRing (MvPolynomial (Fin 4) K)) = 0 := by
    rw [closedGaussCoefficientParameterHom_source_value]
    exact closedGaussParameterField_le_sourceEuler_constants H hH I (e RatFunc.X).property
  have he := homogeneous_coefficientEuler_of_source_weight H hd hH p hY ((f₀) RatFunc.X) 0
    (by simpa only [map_zero, mul_zero, zero_mul] using hsource)
  simpa only [map_zero, zero_mul] using he

omit hGauss in
/-- Every rational coefficient in the constructed graph-normal
parameter has output Euler weight zero. -/
theorem actual_closed_gauss_graph_coefficient_output_euler_zero (r : RatFunc K) :
    coefficientEuler (Y) hY ((f₀) r) = 0 := by
  rw [rational_parameter_chain_rule (f₀) (coefficientEuler (Y) hY) r,
    actual_closed_gauss_graph_parameter_output_euler_zero H I p hY h hh e hd hH, mul_zero]

omit hGauss in
/-- The actual linear ruling denominator has output Euler weight one. -/
theorem actual_closed_gauss_graph_denominator_output_weight :
    coefficientEuler (Y) hY (n₀) = (n₀) := by
  unfold parametricRulingDenominator
  rw [derivation_dotProduct]
  have hcoord (i : Fin 3) : coefficientEuler (Y) hY ((y₀) i) = (y₀) i :=
    coordinate_direction_coordinate (δ₀) (y₀) (y₀) (coefficientPartial_coordinate (Y) hY) i
  simp [dotProduct, actual_closed_gauss_graph_coefficient_output_euler_zero H I p hY h hh e hd hH, hcoord]

omit hGauss in
/-- The actual product nc has precisely the weight 1+1/d used in
the already checked algebraic root-factorization calculation. -/
theorem actual_closed_gauss_first_invariant_product_output_weight
    (c : L) (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p (Y) hY h) :
    coefficientEuler (Y) hY ((n₀) * c) = (1 + (d : L)⁻¹) * ((n₀) * c) := by
  have hcE : coefficientEuler (Y) hY c = (d : L)⁻¹ * c := by
    simpa only [map_inv₀, map_natCast] using firstFiberInvariant_output_weight H hd hH p hY h c hh hc
  rw [Derivation.leibniz, actual_closed_gauss_graph_denominator_output_weight H I p hY h hh e hd hH, hcE]
  simp only [smul_eq_mul]
  ring

end DimensionFourDependence
