import DimensionFourDependence.PlanarActiveNormalization
import DimensionFourDependence.ConstantCoefficientShearTameness

/-! # Restoring the elementary target translations in Proposition 6.3 -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

/-- The two target translations remove the active-origin terms. -/
theorem planar_target_translation (A : Fin 2 → R₄) :
    ∃ T : Aut₄, T ∈ Tame.subgroup K 4 ∧
      ∀ j, T (X j) = X j + ![base4 (planarActiveConstant (A 0)),
        base4 (planarActiveConstant (A 1)), 0, 0] j := by
  let c := base4 (planarActiveConstant (A 0))
  let e := base4 (planarActiveConstant (A 1))
  have hc : (0 : Fin 4) ∉ c.vars := base4_notMem_active _ 0 (by decide) (by decide)
  have he : (1 : Fin 4) ∉ e.vars := base4_notMem_active _ 1 (by decide) (by decide)
  have hce : (0 : Fin 4) ∉ e.vars := base4_notMem_active _ 0 (by decide) (by decide)
  let C₀ : Aut₄ := Tame.elementary 0 c hc
  let C₁ : Aut₄ := Tame.elementary 1 e he
  have hx (j : Fin 4) : C₀ (X j) = X j + if j = 0 then c else 0 :=
    Tame.elementary_X _ _ _ _
  have hy (j : Fin 4) : C₁ (X j) = X j + if j = 1 then e else 0 :=
    Tame.elementary_X _ _ _ _
  have hfix : C₀ e = e := Tame.elementary_fixed _ _ _ hc hce
  refine ⟨C₀ * C₁, (Tame.subgroup K 4).mul_mem
    (Tame.elementary_mem _ _ hc) (Tame.elementary_mem _ _ he), ?_⟩
  intro j
  change (C₀ * C₁) (X j) = X j + ![c, e, 0, 0] j
  rw [AlgEquiv.mul_apply, hy]
  fin_cases j <;> simp [hx, hfix]

/-- The coordinate substitution for the original map is the normalized
substitution applied after the coordinate substitution of the translation. -/
theorem planar_target_translation_restores_original
    (A : Fin 2 → R₄) (F T : Aut₄)
    (hF : ∀ j, F (X j) = X j + ![planarActiveNormalized (A 0), planarActiveNormalized (A 1), 0, 0] j)
    (hT : ∀ j, T (X j) = X j + ![base4 (planarActiveConstant (A 0)),
      base4 (planarActiveConstant (A 1)), 0, 0] j) :
    ∀ j, (F * T) (X j) = X j + ![A 0, A 1, 0, 0] j := by
  have hbase (c : MvPolynomial (Fin 2) K) : F (base4 c) = base4 c := by
    change F.toAlgHom (aeval ![X 2, X 3] c) = aeval ![X 2, X 3] c
    rw [Tame.algHom_aeval]
    have h : (fun i : Fin 2 => F.toAlgHom (![X 2, X 3] i)) = ![X 2, X 3] := by
      funext i
      fin_cases i
      · change F (X 2) = X 2
        simpa using hF 2
      · change F (X 3) = X 3
        simpa using hF 3
    rw [h]
  intro j
  simp only [AlgEquiv.mul_apply, hT, map_add, hF]
  fin_cases j <;> simp [hbase, planarActiveNormalized, sub_add_cancel, add_assoc]

end DimensionFourDependence.Shear
