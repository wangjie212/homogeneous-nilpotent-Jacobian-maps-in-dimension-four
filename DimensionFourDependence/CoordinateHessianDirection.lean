import DimensionFourDependence.IsotropicDirectionDifferentiation

/-! # Constant normalized directions for actual commuting Hessian partials -/

namespace DimensionFourDependence

open Matrix

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- The Hessian formed from a family of coordinate derivations. -/
noncomputable def derivationHessian (δ : Fin n → Derivation K F F) (h : F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => δ i (δ j h)

/-- The corresponding third coefficient derivative tensor. -/
noncomputable def derivationCubicTensor (δ : Fin n → Derivation K F F) (h : F) :
    Fin n → Fin n → Fin n → F := fun i j k => δ i (δ j (δ k h))

theorem derivationHessian_symmetric (δ : Fin n → Derivation K F F)
    (hcomm : ∀ i j a, δ i (δ j a) = δ j (δ i a)) (h : F) (i j : Fin n) :
    derivationHessian δ h i j = derivationHessian δ h j i := hcomm i j h

/-- Differentiating the Hessian along `Z` contracts its third tensor
with `Z` in all three positions. -/
theorem hessian_directional_coefficient_contraction
    (δ : Fin n → Derivation K F F) (hcomm : ∀ i j a, δ i (δ j a) = δ j (δ i a))
    (h : F) (Z : Fin n → F) :
    (∑ i, ∑ j, coordinateEuler Z δ (derivationHessian δ h i j) * Z i * Z j) =
      ∑ i, ∑ j, ∑ k, derivationCubicTensor δ h i j k * Z i * Z j * Z k := by
  simp only [coordinateEuler_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  change Z k * δ k (δ i (δ j h)) * Z i * Z j = δ i (δ j (δ k h)) * Z i * Z j * Z k
  rw [hcomm k i, hcomm k j]
  ring

/-- The actual cubic isotropy condition (3.4) forces `DZ=0` for the
normalized direction, using the rank-two Hessian and its radial radical. -/
theorem normalized_coordinate_hessian_direction_constant [CharZero F]
    (δ : Fin 3 → Derivation K F F) (hcomm : ∀ i j a, δ i (δ j a) = δ j (δ i a))
    (h : F) (hrank : (derivationHessian δ h).rank = 2) (Y Z : Fin 3 → F)
    (hY : (derivationHessian δ h) *ᵥ Y = 0)
    (a b : Fin 3) (hYa : Y a ≠ 0) (hZa : Z a = 0) (hZb : Z b = 1)
    (hZ : matrixBilinearPairing (derivationHessian δ h) Z Z = 0)
    (hCubic : (∑ i, ∑ j, ∑ k, derivationCubicTensor δ h i j k * Z i * Z j * Z k) = 0) :
    (fun i => coordinateEuler Z δ (Z i)) = 0 := by
  apply normalized_isotropic_direction_derivative_zero (coordinateEuler Z δ)
    (derivationHessian δ h) (derivationHessian_symmetric δ hcomm h) hrank Y Z hY a b hYa hZa hZb hZ
  rw [hessian_directional_coefficient_contraction δ hcomm h Z, hCubic]

end DimensionFourDependence
