import DimensionFourDependence.ExtendedProjectiveInfinityChart
import DimensionFourDependence.ParametricGraphBaseChange

/-! # Original boundary coefficient arrays after a specified field extension

The original first leading equation and modified second quadric retain
their exact coefficient-extended values. Extended derivations produce
the mapped original Hessians, so the root-chart constructor's jets are
jets of these same original equations.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {E F : Type*} [Field E] [Field F] {n : ℕ}

/-- The original linear coefficient form preserves its exact value
under the specified coefficient map. -/
theorem linearFormPolynomial_map_coefficients (f : E →+* F) (a : Fin n → E) :
    MvPolynomial.map f (linearFormPolynomial a) = linearFormPolynomial (fun i => f (a i)) := by
  simp only [linearFormPolynomial, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

/-- The original quadratic coefficient array becomes its specified
mapped matrix in the same original coordinate labels. -/
theorem quadraticFormPolynomial_map_coefficients
    (f : E →+* F) (B : Matrix (Fin n) (Fin n) E) :
    MvPolynomial.map f (quadraticFormPolynomial B) = quadraticFormPolynomial (B.map f) := by
  simp only [quadraticFormPolynomial, map_sum, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X, Matrix.map_apply]

/-- The first original leading fiber equation is the leading equation
with precisely its coefficient-extended gradient, Hessian and constant. -/
theorem quadraticFiberPolynomial_leading_map_coefficients
    (f : E →+* F) (a : Fin n → E) (B : Matrix (Fin n) (Fin n) E) (q : E) :
    MvPolynomial.map f (homogeneousComponent 2 (quadraticFiberPolynomial a B q)) =
      homogeneousComponent 2 (quadraticFiberPolynomial (fun i => f (a i)) (B.map f) (f q)) := by
  simp only [quadraticFiberPolynomial_leading_component, map_mul, MvPolynomial.map_C,
    map_inv₀, map_ofNat, quadraticFormPolynomial_map_coefficients]

/-- The original modified second leading equation retains exactly
the mapped coefficient arrays under the specified field embedding. -/
theorem modifiedBoundaryQuadric_map_coefficients
    (f : E →+* F) (a Lambda : Fin 3 → E) (B : Matrix (Fin 3) (Fin 3) E) :
    MvPolynomial.map f (modifiedBoundaryQuadric a Lambda B) =
      modifiedBoundaryQuadric (fun i => f (a i)) (fun i => f (Lambda i)) (B.map f) := by
  simp only [modifiedBoundaryQuadric, map_add, map_neg, map_mul,
    map_ofNat, quadraticFormPolynomial_map_coefficients, linearFormPolynomial_map_coefficients]

variable {K : Type*} [Field K] [Algebra K E] [Algebra K F] [Algebra E F]

/-- A specified extension of each original partial differentiates
the original Hessian twice with its exact coefficient map. -/
theorem derivationHessian_map_of_extended_partials
    (delta : Fin n → Derivation K E E) (Delta : Fin n → Derivation K F F)
    (hext : ∀ i a, Delta i (algebraMap E F a) = algebraMap E F (delta i a)) (a : E) :
    derivationHessian Delta (algebraMap E F a) = (derivationHessian delta a).map (algebraMap E F) := by
  funext i j
  change Delta i (Delta j (algebraMap E F a)) = _
  rw [hext, hext]
  rfl

end DimensionFourDependence
