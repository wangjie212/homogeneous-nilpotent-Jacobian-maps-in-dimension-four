import DimensionFourDependence.BinaryPencilBaseFrame
import DimensionFourDependence.ShearAutomorphism

/-! # Tameness of a scalar shear transports through the base frame -/

namespace DimensionFourDependence.Shear

open Matrix MvPolynomial

set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "M₂" => Matrix (Fin 2) (Fin 2) K

theorem scalar_shear_tame_descends_from_binary_base_change
    (T : M₂) (hT : IsUnit T.det) (a b : R₂) (c : K)
    (h : automorphism4 (linearPolynomialPullback T a) (linearPolynomialPullback T b)
      (C c * X 0) ∈ Tame.subgroup K 4) :
    automorphism4 a b (C c * X 0) ∈ Tame.subgroup K 4 := by
  let α := linearPolynomialPullback T a
  let β := linearPolynomialPullback T b
  let E := binaryPencilBaseFrame T hT
  let F : Aut₄ := automorphism4 a b (C c * X 0)
  let G : Aut₄ := automorphism4 α β (C c * X 0)
  have hE : E ∈ Tame.subgroup K 4 := binaryPencilBaseFrame_tame T hT
  have he (p : R₂) : E (base4 p) = base4 (linearPolynomialPullback T p) :=
    binaryPencilBaseFrame_base T hT p
  have hx : E (X 0) = X 0 := binaryPencilBaseFrame_X_zero T hT
  have hy : E (X 1) = X 1 := binaryPencilBaseFrame_X_one T hT
  have hcomm (d : K) : E (C d) = C d := E.commutes d
  have hs : E (invariant4 a b) = invariant4 α β := by
    simp only [invariant4, map_add, map_mul, he, hx, hy, α, β]
  have hGF (p : R₂) : G (base4 p) = base4 p := substitution4_base α β p (C c * X 0)
  have hF (j : Fin 4) : F (X j) =
      X j + ![C c * base4 b * invariant4 a b, -(C c * base4 a * invariant4 a b), 0, 0] j := by
    rw [← scalar_linear_shear_perturbation]
    exact automorphism4_X _ _ _ _
  have hG (j : Fin 4) : G (X j) =
      X j + ![C c * base4 β * invariant4 α β, -(C c * base4 α * invariant4 α β), 0, 0] j := by
    rw [← scalar_linear_shear_perturbation]
    exact automorphism4_X _ _ _ _
  have hz : E (X 2) = base4 (linearPolynomialPullback T (X 0)) := by
    have he' := he (X 0)
    simpa [base4, aeval_X] using he'
  have ht : E (X 3) = base4 (linearPolynomialPullback T (X 1)) := by
    have he' := he (X 1)
    simpa [base4, aeval_X] using he'
  have h₁ : E.toAlgHom.comp F.toAlgHom = G.toAlgHom.comp E.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    change E (F (X j)) = G (E (X j))
    rw [hF]
    fin_cases j
    · change E (X 0 + C c * base4 b * invariant4 a b) = G (E (X 0))
      rw [map_add, map_mul, map_mul, hcomm, he, hs, hx, hG] <;> rfl
    · change E (X 1 + -(C c * base4 a * invariant4 a b)) = G (E (X 1))
      rw [map_add, map_neg, map_mul, map_mul, hcomm, he, hs, hy, hG] <;> rfl
    · change E (X 2 + 0) = G (E (X 2))
      rw [add_zero, hz, hGF]
    · change E (X 3 + 0) = G (E (X 3))
      rw [add_zero, ht, hGF]
  have h₂ : E * F = G * E := by
    apply AlgEquiv.ext
    exact AlgHom.congr_fun h₁
  have h₃ : F = E⁻¹ * G * E := by
    calc
      F = E⁻¹ * (E * F) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = E⁻¹ * G * E := by rw [h₂, mul_assoc]
  change F ∈ Tame.subgroup K 4
  rw [h₃]
  exact (Tame.subgroup K 4).mul_mem
    ((Tame.subgroup K 4).mul_mem ((Tame.subgroup K 4).inv_mem hE) h) hE

end DimensionFourDependence.Shear
