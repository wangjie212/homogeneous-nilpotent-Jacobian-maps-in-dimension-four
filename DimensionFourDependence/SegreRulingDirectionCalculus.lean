import DimensionFourDependence.ParametricLinearRootForms

/-! # Actual directional calculus on either Segre ruling -/

namespace DimensionFourDependence

open Matrix

universe u
variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- The original ruling relation makes the actual directional derivative
fix the specified coordinate-ratio parameter. -/
theorem segre_ruling_direction_fixes_coordinate_ratio
    (δ : Fin 3 → Derivation K F F) (Y b : Fin 3 → F)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0)
    (hY0 : Y 0 ≠ 0) (j : Fin 3)
    (hruling : b j = (Y j / Y 0) * b 0) :
    coordinateEuler b δ (Y j / Y 0) = 0 := by
  rw [Derivation.leibniz_div, coordinate_direction_coordinate δ Y b hcoord j,
    coordinate_direction_coordinate δ Y b hcoord 0, hruling]
  simp only [smul_eq_mul]
  field_simp [hY0]
  ring

/-- The output Euler derivation fixes each original Segre parameter. -/
theorem segre_output_euler_fixes_coordinate_ratio
    (δ : Fin 3 → Derivation K F F) (Y : Fin 3 → F)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0) (j : Fin 3) :
    coordinateEuler Y δ (Y j / Y 0) = 0 := by
  simpa only [sub_self, zero_mul] using
    derivation_quotient_weight (coordinateEuler Y δ) (Y j) (Y 0) 1 1
      (by simpa only [one_mul] using coordinate_direction_coordinate δ Y Y hcoord j)
      (by simpa only [one_mul] using coordinate_direction_coordinate δ Y Y hcoord 0)

/-- Multiplication by the original radial output raises the exact
Euler weight of the original first invariant by one. -/
theorem segre_radial_product_euler_weight
    (δ : Fin 3 → Derivation K F F) (Y : Fin 3 → F)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0)
    (c θ : F) (hc : coordinateEuler Y δ c = θ * c) :
    coordinateEuler Y δ (Y 0 * c) = (1 + θ) * (Y 0 * c) := by
  rw [Derivation.leibniz, coordinate_direction_coordinate δ Y Y hcoord 0, hc]
  simp only [smul_eq_mul]
  ring

/-- Parameter-algebraicity makes the actual ruling direction constant.
The original Hessian boundary equation therefore gives its actual zero
second directional derivative, with no acceleration assumption. -/
theorem segre_parameter_algebraic_ruling_zero_acceleration
    (p : RatFunc K →ₐ[K] F) (δ : Fin 3 → Derivation K F F) (Y b : Fin 3 → F)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0)
    (hY0 : Y 0 ≠ 0) (j : Fin 3) (hp : p RatFunc.X = Y j / Y 0)
    (hruling : b j = (Y j / Y 0) * b 0)
    (halg : ∀ i, IsAlgebraic p.fieldRange (b i)) (f : F)
    (hHess : matrixBilinearPairing (derivationHessian δ f) b b = 0) :
    coordinateEuler b δ (coordinateEuler b δ f) = 0 := by
  have ht : coordinateEuler b δ (p RatFunc.X) = 0 := by
    rw [hp]
    exact segre_ruling_direction_fixes_coordinate_ratio δ Y b hcoord hY0 j hruling
  have hb (i : Fin 3) : coordinateEuler b δ (b i) = 0 :=
    parameter_algebraic_coefficient_direction_constant p (coordinateEuler b δ) ht (b i) (halg i)
  rw [coordinate_direction_second_derivative δ b hb]
  exact hHess

end DimensionFourDependence
