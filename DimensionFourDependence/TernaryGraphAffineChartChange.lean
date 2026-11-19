import DimensionFourDependence.TernaryGraphCovectorRestriction
import DimensionFourDependence.ModifiedCubicFiberBoundary
import DimensionFourDependence.ConjugateOutputConstants

/-! # An original frame changes the projected ternary graph by affine substitution -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u v
set_option maxHeartbeats 1850000

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The old affine expression for one new source coordinate. -/
noncomputable def ternaryGraphProjectedCoordinatePolynomial (p q s : L) (l : Fin 3 → K) :
    MvPolynomial (Fin 2) L :=
  C (algebraMap K L (l 2) * s) + linearFormPolynomial (ternaryGraphRestrictedCovector p q l)

theorem ternaryGraphProjectedCoordinatePolynomial_totalDegree_le
    (p q s : L) (l : Fin 3 → K) :
    (ternaryGraphProjectedCoordinatePolynomial p q s l).totalDegree ≤ 1 :=
  (totalDegree_add _ _).trans (max_le (by simp only [totalDegree_C, Nat.zero_le])
    (linearFormPolynomial_totalDegree _))

theorem ternaryGraphProjectedCoordinatePolynomial_leading_component
    (p q s : L) (l : Fin 3 → K) :
    homogeneousComponent 1 (ternaryGraphProjectedCoordinatePolynomial p q s l) =
      linearFormPolynomial (ternaryGraphRestrictedCovector p q l) := by
  rw [ternaryGraphProjectedCoordinatePolynomial, map_add,
    homogeneousComponent_eq_zero _ _ (by simp only [totalDegree_C, zero_lt_one]), zero_add,
    homogeneousComponent_eq_self (linearFormPolynomial_homogeneous _)]

theorem ternaryGraphProjectedCoordinatePolynomial_aeval
    {A : Type v} [Field A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
    (p q s : L) (l : Fin 3 → K) (e : Fin 2 → A) :
    aeval e (ternaryGraphProjectedCoordinatePolynomial p q s l) =
      ∑ j, algebraMap K A (l j) *
        (![e 0, e 1, algebraMap L A s + algebraMap L A p * e 0 + algebraMap L A q * e 1] :
          Fin 3 → A) j := by
  simp only [ternaryGraphProjectedCoordinatePolynomial, linearFormPolynomial, Fin.sum_univ_three,
    Fin.sum_univ_two]
  simp only [map_add, map_mul, aeval_C, aeval_X]
  change algebraMap L A (algebraMap K L (l 2)) * algebraMap L A s +
      (algebraMap L A (algebraMap K L (l 0) + algebraMap K L (l 2) * p) * e 0 +
        algebraMap L A (algebraMap K L (l 1) + algebraMap K L (l 2) * q) * e 1) =
    algebraMap K A (l 0) * e 0 + algebraMap K A (l 1) * e 1 +
      algebraMap K A (l 2) * (algebraMap L A s + algebraMap L A p * e 0 + algebraMap L A q * e 1)
  simp only [map_add, map_mul, ← IsScalarTower.algebraMap_apply K L A]
  ring

/-- An invertible restriction of the two frame rows gives an injective
pullback on the highest homogeneous component. -/
theorem ternaryGraphProjectedCoordinatePolynomial_leading_pullback_injective
    (p q s : L) (l : Fin 2 → (Fin 3 → K))
    (hdet : (show Matrix (Fin 2) (Fin 2) L from fun i =>
      ternaryGraphRestrictedCovector p q (l i)).det ≠ 0) :
    Function.Injective (aeval (fun i => homogeneousComponent 1
      (ternaryGraphProjectedCoordinatePolynomial p q s (l i))) :
      MvPolynomial (Fin 2) L →ₐ[L] MvPolynomial (Fin 2) L) := by
  classical
  let B : Matrix (Fin 2) (Fin 2) L := fun i => ternaryGraphRestrictedCovector p q (l i)
  have hB : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  have hleft : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have hright : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have he : (fun i => homogeneousComponent 1
      (ternaryGraphProjectedCoordinatePolynomial p q s (l i))) = linearPolynomialMap B := by
    funext i
    exact ternaryGraphProjectedCoordinatePolynomial_leading_component p q s (l i)
  rw [he]
  exact (matrixPolynomialCoordinateEquiv B B⁻¹ hleft hright).injective

local notation "F" => FractionRing (MvPolynomial (Fin 3) K)
local notation "x" => (rationalCoordinate (K := K) (n := 3))

/-- Evaluating the affine expression in the old chart and applying
the source automorphism gives the actual new source coordinate. -/
theorem ternaryGraphProjectedCoordinatePolynomial_source_value
    [Algebra L F] [IsScalarTower K L F]
    (T S : Matrix (Fin 3) (Fin 3) K) (hTS : T * S = 1) (hST : S * T = 1)
    (p q s : L)
    (hplane : x 2 = algebraMap L F s + algebraMap L F p * x 0 + algebraMap L F q * x 1)
    (i : Fin 2) :
    matrixSourceFractionEquiv T S hTS hST
      (aeval (fun j : Fin 2 => x j.castSucc)
        (ternaryGraphProjectedCoordinatePolynomial p q s (S i.castSucc))) = x i.castSucc := by
  let e := matrixSourceFractionEquiv T S hTS hST
  have hx : (![x 0, x 1, algebraMap L F s + algebraMap L F p * x 0 + algebraMap L F q * x 1] :
      Fin 3 → F) = x := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact hplane.symm
  have h : aeval (fun j : Fin 2 => x j.castSucc)
        (ternaryGraphProjectedCoordinatePolynomial p q s (S i.castSucc)) = e.symm (x i.castSucc) := by
    rw [ternaryGraphProjectedCoordinatePolynomial_aeval]
    change (∑ j, algebraMap K F (S i.castSucc j) *
        (![x 0, x 1, algebraMap L F s + algebraMap L F p * x 0 + algebraMap L F q * x 1] :
          Fin 3 → F) j) = _
    rw [hx]
    exact (matrixSourceFractionEquiv_symm_coordinate T S hTS hST i.castSucc).symm
  change e _ = x i.castSucc
  rw [h, e.apply_symm_apply]

end DimensionFourDependence
