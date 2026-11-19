import DimensionFourDependence.PlanarShearCoefficientRing
import DimensionFourDependence.ConstantCoefficientShearTameness

/-! # Proposition 6.3: removing the actual active-origin constants -/

namespace DimensionFourDependence.Shear

open Matrix MvPolynomial

set_option maxHeartbeats 500000

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "A₂" => MvPolynomial (Fin 2) R₂

/-- The actual base coefficient at the active origin. -/
noncomputable def planarActiveConstant (p : R₄) : R₂ :=
  aeval (fun _ : Fin 2 => (0 : R₂)) (planarCoefficientEquiv p)

noncomputable def planarActiveNormalized (p : R₄) : R₄ := p - base4 (planarActiveConstant p)

theorem base4_planarActiveConstant (p : R₄) :
    base4 (planarActiveConstant p) = aeval (![0,0,X 2,X 3] : Fin 4 → R₄) p := by
  let ev : A₂ →ₐ[K] R₂ := (aeval (fun _ : Fin 2 => (0 : R₂))).restrictScalars K
  have he : (aeval (![X 2,X 3] : Fin 2 → R₄)).comp
      (ev.comp (planarCoefficientEquiv (K := K)).toAlgHom) =
        aeval (![0,0,X 2,X 3] : Fin 4 → R₄) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X, AlgEquiv.coe_toAlgHom]
    have hx (j : Fin 2) : ev (planarCoefficientEquiv (X (j.castAdd 2))) = 0 := by
      rw [planarCoefficientEquiv_X_active]
      exact aeval_X _ _
    have hy (j : Fin 2) : ev (planarCoefficientEquiv (X (Fin.natAdd 2 j))) = X j := by
      rw [planarCoefficientEquiv_X_base]
      change (aeval (fun _ : Fin 2 => (0 : R₂))) (C (X j)) = X j
      simp
    fin_cases i
    · change aeval ![X 2,X 3] (ev (planarCoefficientEquiv (X ((0 : Fin 2).castAdd 2)))) = 0
      rw [hx, map_zero]
    · change aeval ![X 2,X 3] (ev (planarCoefficientEquiv (X ((1 : Fin 2).castAdd 2)))) = 0
      rw [hx, map_zero]
    · change aeval ![X 2,X 3] (ev (planarCoefficientEquiv (X (Fin.natAdd 2 (0 : Fin 2))))) = X 2
      rw [hy, aeval_X]
      rfl
    · change aeval ![X 2,X 3] (ev (planarCoefficientEquiv (X (Fin.natAdd 2 (1 : Fin 2))))) = X 3
      rw [hy, aeval_X]
      rfl
  exact AlgHom.congr_fun he p

theorem planarActiveNormalized_isHomogeneous (p : R₄) {d : ℕ} (hp : p.IsHomogeneous d) :
    (planarActiveNormalized p).IsHomogeneous d := by
  unfold planarActiveNormalized
  rw [base4_planarActiveConstant]
  have h (i : Fin 4) : ((![0,0,X 2,X 3] : Fin 4 → R₄) i).IsHomogeneous 1 := by
    fin_cases i
    · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_X _ _
  exact hp.sub (by simpa only [one_mul] using hp.aeval _ h)

theorem planarCoefficientEquiv_normalized_at_origin (p : R₄) :
    aeval (fun _ : Fin 2 => (0 : R₂)) (planarCoefficientEquiv (planarActiveNormalized p)) = 0 := by
  rw [planarActiveNormalized, map_sub, planarCoefficientEquiv_base4, map_sub, aeval_C]
  change planarActiveConstant p - planarActiveConstant p = 0
  exact sub_self _

/-- The original active block, with both fixed variables retained. -/
noncomputable def planarActiveJacobian (A : Fin 2 → R₄) : Matrix (Fin 2) (Fin 2) R₄ :=
  of fun i j => pderiv (j.castAdd 2) (A i)

theorem planarActiveJacobian_normalized (A : Fin 2 → R₄) :
    planarActiveJacobian (fun i => planarActiveNormalized (A i)) = planarActiveJacobian A := by
  have h (p : R₂) (j : Fin 2) : pderiv (j.castAdd 2) (base4 p) = 0 := by
    fin_cases j <;> exact pderiv_base4_active p _ (by decide) (by decide)
  funext i j
  simp [planarActiveJacobian, planarActiveNormalized, h]

end DimensionFourDependence.Shear
