import DimensionFourDependence.ActivePencilPerturbationConjugacy
import DimensionFourDependence.QuinticCommutatorCoordinates
import DimensionFourDependence.ShearAutomorphism

/-! # The exact polynomial coordinate formula (6.15) -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 2100000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "x" => (X 0 : R₄)
local notation "y" => (X 1 : R₄)
local notation "z" => (X 2 : R₄)
local notation "t" => (X 3 : R₄)
theorem normalized_quintic_shear_X (η scale : K) (j : Fin 4) :
    let S := quinticInvariant (C η) x y z t
    Shear.automorphism4 (X 0 * X 1) (X 0 ^ 2 + C η * X 1 ^ 2)
        (C scale * X 0) (X j) =
      ![x + C scale * (z ^ 2 + C η * t ^ 2) * S, y - C scale * (z * t) * S, z, t] j := by
  let a : R₂ := X 0 * X 1
  let d : R₂ := X 0 ^ 2 + C η * X 1 ^ 2
  have ha : Shear.base4 a = z * t := by simp [a, Shear.base4]
  have hd : Shear.base4 d = z ^ 2 + C η * t ^ 2 := by simp [d, Shear.base4]
  have hS : Shear.invariant4 a d = quinticInvariant (C η) x y z t := by
    unfold Shear.invariant4 quinticInvariant
    rw [ha, hd]
  change Shear.automorphism4 a d (C scale * X 0) (X j) = _
  rw [Shear.automorphism4_X, Shear.scalar_linear_shear_perturbation, ha, hd, hS]
  fin_cases j <;> simp [sub_eq_add_neg]

end DimensionFourDependence.Quintic
