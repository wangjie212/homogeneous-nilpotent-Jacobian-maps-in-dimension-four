import DimensionFourDependence.RationalParameterDerivation
import DimensionFourDependence.CoordinateHessianDirection
import DimensionFourDependence.ImageNormalDerivation

/-! # Constructing the graph Hessian and denominator in (4.1)

The rational parameter chain rule and the ruling equation derive the
nonzero denominator, parameter differential and rank-one Hessian formula.
-/

namespace DimensionFourDependence

open Matrix

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- Differentiating a parameter-dependent linear form in the actual
coordinate system retains both its parameter and coordinate terms. -/
theorem rational_parameter_linear_pairing_partial
    (f : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K) (j : Fin n) :
    δ j ((fun i => f (A i)) ⬝ᵥ y) =
      ((fun i => f (rationalParameterDerivative K (A i))) ⬝ᵥ y) * δ j (f RatFunc.X) + f (A j) := by
  rw [derivation_dotProduct]
  have hchain : (fun i => δ j (f (A i))) =
      (fun i => f (rationalParameterDerivative K (A i)) * δ j (f RatFunc.X)) :=
    funext (fun i => rational_parameter_chain_rule f (δ j) (A i))
  rw [hchain]
  have hleft : (fun i => f (rationalParameterDerivative K (A i)) * δ j (f RatFunc.X)) ⬝ᵥ y =
      ((fun i => f (rationalParameterDerivative K (A i))) ⬝ᵥ y) * δ j (f RatFunc.X) := by
    simp only [dotProduct, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft]
  congr 1
  simp [dotProduct, hcoord, mul_ite]

/-- The ruling denominator n=A''(t) dot Y in the original graph coordinates. -/
noncomputable def parametricRulingDenominator
    (f : RatFunc K →ₐ[K] F) (A : Fin n → RatFunc K) (y : Fin n → F) : F :=
  (fun i => f (rationalParameterDerivative K (rationalParameterDerivative K (A i)))) ⬝ᵥ y

/-- Differentiating the ruling equation constructs n times each
coordinate derivative of the parameter, before division by n. -/
theorem parametric_ruling_denominator_times_parameter_partial
    (f : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => f (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0) (j : Fin n) :
    parametricRulingDenominator f A y * δ j (f RatFunc.X) =
      -f (rationalParameterDerivative K (A j)) := by
  have he := congrArg (δ j) htangent
  rw [rational_parameter_linear_pairing_partial f δ y hcoord, map_zero] at he
  change parametricRulingDenominator f A y * δ j (f RatFunc.X) +
    f (rationalParameterDerivative K (A j)) = 0 at he
  exact eq_neg_of_add_eq_zero_left he

/-- The nonconstant normal derivative and ruling relation force
the denominator in (4.1) to be nonzero; this is not an extra hypothesis. -/
theorem parametric_ruling_denominator_ne_zero
    (f : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => f (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => f (rationalParameterDerivative K (A i))) ≠ 0) :
    parametricRulingDenominator f A y ≠ 0 := by
  intro hz
  apply hfirst
  funext j
  have he := parametric_ruling_denominator_times_parameter_partial f δ y hcoord A htangent j
  rw [hz, zero_mul] at he
  exact neg_eq_zero.mp he.symm

/-- The actual coordinate differential of the ruling parameter in (4.1). -/
theorem parametric_ruling_parameter_partial
    (f : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => f (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => f (rationalParameterDerivative K (A i))) ≠ 0) (j : Fin n) :
    δ j (f RatFunc.X) = -f (rationalParameterDerivative K (A j)) / parametricRulingDenominator f A y := by
  apply (eq_div_iff (parametric_ruling_denominator_ne_zero f δ y hcoord A htangent hfirst)).mpr
  rw [mul_comm]
  exact parametric_ruling_denominator_times_parameter_partial f δ y hcoord A htangent j

/-- The graph gradient and ruling equation derive the entire actual
rank-one Hessian formula (4.1), with the original coordinate labels. -/
theorem parametric_graph_hessian_formula
    (f : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => f (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => f (rationalParameterDerivative K (A i))) ≠ 0)
    (h : F) (hgradient : ∀ i, δ i h = f (A i)) (i j : Fin n) :
    derivationHessian δ h i j =
      -(f (rationalParameterDerivative K (A i)) * f (rationalParameterDerivative K (A j))) /
        parametricRulingDenominator f A y := by
  change δ i (δ j h) = _
  rw [hgradient, rational_parameter_chain_rule,
    parametric_ruling_parameter_partial f δ y hcoord A htangent hfirst]
  ring

/-- Differentiating the actual ruling denominator retains its explicit
coordinate term and its third-normal-derivative parameter term. -/
theorem parametric_ruling_denominator_partial
    (f : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => f (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => f (rationalParameterDerivative K (A i))) ≠ 0) (j : Fin n) :
    δ j (parametricRulingDenominator f A y) =
      f (rationalParameterDerivative K (rationalParameterDerivative K (A j))) -
        ((fun i => f (rationalParameterDerivative K (rationalParameterDerivative K
          (rationalParameterDerivative K (A i))))) ⬝ᵥ y) *
          f (rationalParameterDerivative K (A j)) / parametricRulingDenominator f A y := by
  unfold parametricRulingDenominator
  rw [rational_parameter_linear_pairing_partial f δ y hcoord,
    parametric_ruling_parameter_partial f δ y hcoord A htangent hfirst]
  unfold parametricRulingDenominator
  ring

/-- Euler's identity and one nonzero parameter partial derive the
ruling equation from the actual parametric graph gradient. -/
theorem parametric_graph_ruling_equation_of_euler
    (f : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K) (h : F) (hgradient : ∀ i, δ i h = f (A i))
    (heuler : coordinateEuler y δ h = h)
    (hparameter : ∃ j, δ j (f RatFunc.X) ≠ 0) :
    (fun i => f (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0 := by
  have he : (fun i => f (A i)) ⬝ᵥ y = h := by
    simpa only [coordinateEuler_apply, hgradient, dotProduct, mul_comm] using heuler
  obtain ⟨j, hj⟩ := hparameter
  have hp := congrArg (δ j) he
  rw [rational_parameter_linear_pairing_partial f δ y hcoord, hgradient] at hp
  have hz : ((fun i => f (rationalParameterDerivative K (A i))) ⬝ᵥ y) * δ j (f RatFunc.X) = 0 := by
    linear_combination hp
  exact (mul_eq_zero.mp hz).resolve_right hj

/-- A nonzero actual Hessian forces the parameter derivative of its
graph gradient to be nonzero, with no normal-jet hypothesis. -/
theorem parametric_graph_gradient_derivative_ne_zero
    (f : RatFunc K →ₐ[K] F) (δ : Fin n → Derivation K F F)
    (A : Fin n → RatFunc K) (h : F) (hgradient : ∀ i, δ i h = f (A i))
    (hHess : derivationHessian δ h ≠ 0) :
    (fun i => f (rationalParameterDerivative K (A i))) ≠ 0 := by
  intro hz
  apply hHess
  ext i j
  change δ i (δ j h) = 0
  rw [hgradient, rational_parameter_chain_rule, congrFun hz j, Pi.zero_apply, zero_mul]

end DimensionFourDependence
