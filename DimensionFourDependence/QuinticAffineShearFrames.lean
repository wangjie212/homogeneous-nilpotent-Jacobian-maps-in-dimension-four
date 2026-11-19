import DimensionFourDependence.QuinticDeterminantShearCoordinates

/-! # The affine determinant-shear frames used by the quintic lifts -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

noncomputable def xyShearFrame : Aut₄ :=
  AlgEquiv.ofAlgHom (aeval (![X 0, -X 1, X 3, X 2] : Fin 4 → R₄))
    (aeval (![X 0, -X 1, X 3, X 2] : Fin 4 → R₄))
    (by apply MvPolynomial.algHom_ext; intro j; fin_cases j <;> simp)
    (by apply MvPolynomial.algHom_ext; intro j; fin_cases j <;> simp)

theorem xyShearFrame_X (j : Fin 4) :
    xyShearFrame (X j : R₄) = ![X 0, -X 1, X 3, X 2] j :=
  aeval_X _ _

theorem xyShearFrame_tame : xyShearFrame (K := K) ∈ Tame.subgroup K 4 := by
  apply Subgroup.subset_closure
  left
  intro j
  rw [xyShearFrame_X]
  fin_cases j <;> simp

/-- The coefficient coordinate is shifted by c, so both offsets from
the quintic factorization use the same affine frame. -/
noncomputable def xzShearFrame (c : K) : Aut₄ :=
  AlgEquiv.ofAlgHom (aeval (![X 0, -X 2, X 3, X 1 + C c] : Fin 4 → R₄))
    (aeval (![X 0, X 3 - C c, -X 1, X 2] : Fin 4 → R₄))
    (by
      apply MvPolynomial.algHom_ext
      intro j
      fin_cases j <;> simp)
    (by
      apply MvPolynomial.algHom_ext
      intro j
      fin_cases j <;> simp)

theorem xzShearFrame_X (c : K) (j : Fin 4) :
    xzShearFrame c (X j : R₄) = ![X 0, -X 2, X 3, X 1 + C c] j :=
  aeval_X _ _

theorem xzShearFrame_tame (c : K) : xzShearFrame c ∈ Tame.subgroup K 4 := by
  have h : (X 1 + C c : R₄).totalDegree ≤ 1 := by
    exact (totalDegree_add _ _).trans (by simp)
  apply Subgroup.subset_closure
  left
  intro j
  rw [xzShearFrame_X]
  fin_cases j <;> simp [h]

end DimensionFourDependence.Quintic
