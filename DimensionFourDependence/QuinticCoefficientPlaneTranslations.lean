import DimensionFourDependence.QuinticAffineShearFrames

/-! # Elementary translations with parameters in K[y,t] -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

noncomputable def coefficientPlane : R₂ →ₐ[K] R₄ := aeval ![X 1, X 3]

theorem coefficientPlane_fixed (E : Aut₄) (hy : E (X 1) = X 1) (ht : E (X 3) = X 3)
    (p : R₂) : E (coefficientPlane p) = coefficientPlane p := by
  have h : E.toAlgHom.comp coefficientPlane = coefficientPlane := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [coefficientPlane, AlgHom.comp_apply, aeval_X, AlgEquiv.coe_toAlgHom]
    fin_cases j
    · exact hy
    · exact ht
  exact AlgHom.congr_fun h p

theorem coefficientPlane_notMem (p : R₂) (j : Fin 4) (hy : j ≠ 1) (ht : j ≠ 3) :
    j ∉ (coefficientPlane p).vars := by
  apply Tame.notMem_vars_aeval
  intro i
  fin_cases i <;> simp [hy, ht]

/-- Adding two independent polynomials of y,t to the x and z
coordinates is a product of actual elementary maps. -/
theorem coefficientPlane_double_translation (p q : R₂) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧ ∀ i,
      E (X i) = ![X 0 + coefficientPlane p, X 1, X 2 + coefficientPlane q, X 3] i := by
  have hp := coefficientPlane_notMem p 0 (by decide) (by decide)
  have hq := coefficientPlane_notMem q 2 (by decide) (by decide)
  let P := Tame.elementary 0 (coefficientPlane p) hp
  let Q := Tame.elementary 2 (coefficientPlane q) hq
  have hP (i : Fin 4) : P (X i) = X i + if i = 0 then coefficientPlane p else 0 :=
    Tame.elementary_X _ _ _ i
  have hQ (i : Fin 4) : Q (X i) = X i + if i = 2 then coefficientPlane q else 0 :=
    Tame.elementary_X _ _ _ i
  have hPq : P (coefficientPlane q) = coefficientPlane q :=
    Tame.elementary_fixed _ _ _ hp (coefficientPlane_notMem q 0 (by decide) (by decide))
  refine ⟨P * Q, (Tame.subgroup K 4).mul_mem (Tame.elementary_mem _ _ _) (Tame.elementary_mem _ _ _), ?_⟩
  intro i
  rw [AlgEquiv.mul_apply, hQ]
  fin_cases i <;> simp [hP, hPq]

end DimensionFourDependence.Quintic
