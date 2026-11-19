import DimensionFourDependence.ConjugateOutputConstants
import DimensionFourDependence.OutputCoordinates

/-! # A constant frame transports the original invariant derivation -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 1850000

variable {K : Type*} [Field K] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K
local notation "F" => FractionRing R₀
local notation "ι" => (algebraMap R₀ F)
local notation "x" => (rationalCoordinate (K := K) (n := n))

/-- The transported derivation uses the inverse matrix on the source
direction and the same field automorphism on its entries. -/
theorem transportDerivation_matrixSourceFractionEquiv_coordinate
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (D : Derivation K F F) (i : Fin n) :
    transportDerivation (matrixSourceFractionEquiv T S hTS hST) D (x i) =
      ∑ j, algebraMap K F (S i j) * matrixSourceFractionEquiv T S hTS hST (D (x j)) := by
  rw [transportDerivation_apply, matrixSourceFractionEquiv_symm_coordinate, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [D.leibniz, D.map_algebraMap]
  simp [smul_eq_mul, AlgEquiv.commutes]

/-- Invariance of the direction entries is preserved by a constant
linear coordinate change. -/
theorem transported_invariant_derivation_direction_is_invariant
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (D : Derivation K F F) (hD : ∀ j, D (D (x j)) = 0) (i : Fin n) :
    let D' := transportDerivation (matrixSourceFractionEquiv T S hTS hST) D
    D' (D' (x i)) = 0 := by
  let e := matrixSourceFractionEquiv T S hTS hST
  let D' := transportDerivation e D
  change D' (D' (x i)) = 0
  rw [show D' (x i) = ∑ j, algebraMap K F (S i j) * e (D (x j)) from
    transportDerivation_matrixSourceFractionEquiv_coordinate T S hTS hST D i]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  have h : D' (e (D (x j))) = 0 := by
    rw [transportDerivation_apply_image, hD, map_zero]
  rw [D'.leibniz, h, D'.map_algebraMap]
  simp

/-- Source transport and the inverse constant output frame preserve
annihilation of all polynomial outputs. -/
theorem transported_derivation_kills_linearPolynomialConjugate
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (D : Derivation K F F) (H : Fin n → R₀)
    (hD : ∀ j, D (ι (H j)) = 0) (i : Fin n) :
    transportDerivation (matrixSourceFractionEquiv T S hTS hST) D
      (ι (linearPolynomialConjugate T S H i)) = 0 := by
  let e := matrixSourceFractionEquiv T S hTS hST
  let D' := transportDerivation e D
  have hp (j : Fin n) : ι (linearPolynomialPullback T (H j)) = e (ι (H j)) :=
    (matrixSourceFractionEquiv_polynomial T S hTS hST (H j)).symm
  have h (j : Fin n) : D' (e (ι (H j))) = 0 := by
    rw [transportDerivation_apply_image, hD, map_zero]
  change D' (ι (∑ j, C (S i j) * linearPolynomialPullback T (H j))) = 0
  simp only [map_sum, map_mul, hp, ← algebraMap_eq, ← IsScalarTower.algebraMap_apply K R₀ F]
  apply Finset.sum_eq_zero
  intro j _
  rw [D'.leibniz, h, D'.map_algebraMap]
  simp

end DimensionFourDependence
