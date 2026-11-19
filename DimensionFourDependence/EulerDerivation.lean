import DimensionFourDependence.CoefficientChainRule

/-! # Euler derivations for commuting coordinate partials

Differentiation lowers Euler weight by one. The statements apply to the
actual extended coordinate derivatives, including algebraic coefficients.
-/

namespace DimensionFourDependence

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- The Euler derivation belonging to a coordinate system and its partials. -/
noncomputable def coordinateEuler (y : Fin n → F) (δ : Fin n → Derivation K F F) :
    Derivation K F F := ∑ i, y i • δ i

theorem coordinateEuler_apply (y : Fin n → F) (δ : Fin n → Derivation K F F) (a : F) :
    coordinateEuler y δ a = ∑ i, y i * δ i a := by
  simp only [coordinateEuler, sum_apply, Derivation.smul_apply, smul_eq_mul]

/-- The commutator of a coordinate partial with the Euler derivation is that partial. -/
theorem coordinatePartial_euler (y : Fin n → F) (δ : Fin n → Derivation K F F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j a, δ i (δ j a) = δ j (δ i a)) (j : Fin n) (a : F) :
    δ j (coordinateEuler y δ a) = coordinateEuler y δ (δ j a) + δ j a := by
  simp only [coordinateEuler_apply, map_sum, Derivation.leibniz, smul_eq_mul,
    hcoord, hcomm j, Finset.sum_add_distrib]
  congr 1
  simp [apply_ite]

/-- A partial derivative of a weight-`w` element has weight `w-1`. -/
theorem coordinateEuler_partial_weight (y : Fin n → F) (δ : Fin n → Derivation K F F)
    (hcoord : ∀ i j, δ i (y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j a, δ i (δ j a) = δ j (δ i a))
    (a : F) (w : K) (ha : coordinateEuler y δ a = algebraMap K F w * a) (j : Fin n) :
    coordinateEuler y δ (δ j a) = algebraMap K F (w - 1) * δ j a := by
  have he := congrArg (δ j) ha
  rw [coordinatePartial_euler y δ hcoord hcomm, (δ j).leibniz,
    (δ j).map_algebraMap, smul_zero, add_zero] at he
  simp only [smul_eq_mul] at he
  rw [map_sub, map_one]
  linear_combination he

end DimensionFourDependence
