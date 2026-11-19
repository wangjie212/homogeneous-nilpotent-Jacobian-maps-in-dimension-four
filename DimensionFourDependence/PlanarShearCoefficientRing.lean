import DimensionFourDependence.ShearJacobian

/-! # View the original four-variable polynomials as active binary polynomials over `K[z,t]` -/

namespace DimensionFourDependence.Shear

open Matrix MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "A₂" => MvPolynomial (Fin 2) R₂

/-- The actual coefficient-ring regrouping, retaining the original
order `x,y,z,t`. -/
noncomputable def planarCoefficientEquiv : R₄ ≃ₐ[K] A₂ :=
  (renameEquiv K (finSumFinEquiv (m := 2) (n := 2)).symm).trans (sumAlgEquiv K (Fin 2) (Fin 2))

theorem planarCoefficientEquiv_X_active (i : Fin 2) :
    planarCoefficientEquiv (X (i.castAdd 2) : R₄) = (X i : A₂) := by
  have hi : (finSumFinEquiv (m := 2) (n := 2)).symm (i.castAdd 2) = Sum.inl i :=
    (finSumFinEquiv (m := 2) (n := 2)).symm_apply_apply (Sum.inl i)
  simp [planarCoefficientEquiv, hi, sumAlgEquiv_X_inl]

theorem planarCoefficientEquiv_X_base (i : Fin 2) :
    planarCoefficientEquiv (X (Fin.natAdd 2 i) : R₄) = (C (X i) : A₂) := by
  have hi : (finSumFinEquiv (m := 2) (n := 2)).symm (Fin.natAdd 2 i) = Sum.inr i :=
    (finSumFinEquiv (m := 2) (n := 2)).symm_apply_apply (Sum.inr i)
  rw [planarCoefficientEquiv, AlgEquiv.trans_apply]
  change (sumAlgEquiv K (Fin 2) (Fin 2)) (rename _ (X (Fin.natAdd 2 i))) = _
  rw [rename_X, hi, sumAlgEquiv_X_inr]

theorem planarCoefficientEquiv_C (c : K) : planarCoefficientEquiv (C c : R₄) = (C (C c) : A₂) := by
  rw [planarCoefficientEquiv, AlgEquiv.trans_apply]
  change (sumAlgEquiv K (Fin 2) (Fin 2)) (rename _ (C c)) = _
  rw [rename_C, sumAlgEquiv_C_inl]

theorem planarCoefficientEquiv_base4 (p : R₂) : planarCoefficientEquiv (base4 p) = (C p : A₂) := by
  have he : (planarCoefficientEquiv (K := K)).toAlgHom.comp (aeval ![X 2, X 3]) =
      IsScalarTower.toAlgHom K R₂ A₂ := by
    apply MvPolynomial.algHom_ext
    intro j
    have hj : (planarCoefficientEquiv (K := K)) ((![X 2, X 3] : Fin 2 → R₄) j) = (C (X j) : A₂) := by
      fin_cases j
      · exact planarCoefficientEquiv_X_base (0 : Fin 2)
      · exact planarCoefficientEquiv_X_base (1 : Fin 2)
    rw [AlgHom.comp_apply, aeval_X]
    exact hj
  exact AlgHom.congr_fun he p

/-- Differentiation in either active variable commutes with the actual
regrouping into polynomials over `K[z,t]`. -/
theorem planarCoefficientEquiv_pderiv_active (i : Fin 2) (p : R₄) :
    planarCoefficientEquiv (pderiv (i.castAdd 2) p) = pderiv i (planarCoefficientEquiv p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [planarCoefficientEquiv_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    refine Fin.addCases (m := 2) (n := 2) (fun j => ?_) (fun j => ?_) j
    · simp only [pderiv_mul, map_mul, map_add, hp, planarCoefficientEquiv_X_active, pderiv_X, Pi.single_apply,
        Fin.castAdd_inj]
      split <;> simp
    · have hne : (i.castAdd 2 : Fin 4) ≠ Fin.natAdd 2 j := by
        intro h
        have hh := congrArg Fin.val h
        have hi := i.isLt
        have hj := j.isLt
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
        omega
      have he := planarCoefficientEquiv_X_base (K := K) j
      change planarCoefficientEquiv (pderiv (i.castAdd 2) (p * X (Fin.natAdd 2 j))) = _
      simp only [pderiv_mul, map_add, map_mul, hp, he, pderiv_C, pderiv_X, Pi.single_apply,
        if_neg (Ne.symm hne), map_zero, mul_zero, add_zero]

end DimensionFourDependence.Shear
