import DimensionFourDependence.HomogeneousDehomogenize

/-! # A nonzero homogeneous binary form imposes algebraicity on its affine slope -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 1500000

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem homogeneous_binary_first_chart_nonzero
    (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0) {d : ℕ} (hh : p.IsHomogeneous d) :
    aeval (![1, Polynomial.X] : Fin 2 → Polynomial K) p ≠ 0 := by
  let q : Polynomial K := aeval ![1, Polynomial.X] p
  let e := finSuccEquiv 1
  let B := (projectiveDehomogenize (R := K) (σ := Fin 1)).comp (rename e)
  let E := uniqueAlgEquiv K (Fin 1)
  have he : aeval (![1, Polynomial.X] : Fin 2 → Polynomial K) = E.toAlgHom.comp B := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [aeval_X, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, B, rename_X]
    fin_cases i
    · change (1 : Polynomial K) = E (projectiveDehomogenize (X (none : Option (Fin 1))))
      rw [projectiveDehomogenize_X_none, map_one]
    · change (Polynomial.X : Polynomial K) = E (projectiveDehomogenize (X (some (0 : Fin 1))))
      rw [projectiveDehomogenize_X_some]
      change Polynomial.X = eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X)
        (X 0 : MvPolynomial (Fin 1) K)
      rw [eval₂_X]
  have hq : q ≠ 0 := by
    intro hz
    have hq' : E (projectiveDehomogenize (rename e p)) = 0 :=
      (AlgHom.congr_fun he p).symm.trans hz
    have hd : projectiveDehomogenize (rename e p) = 0 := E.injective (hq'.trans (map_zero E).symm)
    have hzero := homogeneous_dehomogenize_eq_zero _ hh.rename_isHomogeneous hd
    apply hp
    apply (renameEquiv K e).injective
    exact hzero.trans (map_zero (renameEquiv K e)).symm
  exact hq

theorem eval_binary_first_chart (p : MvPolynomial (Fin 2) K) (s : F) :
    Polynomial.aeval s (aeval (![1, Polynomial.X] : Fin 2 → Polynomial K) p) =
      aeval ![1, s] p := by
  rw [comp_aeval_apply]
  have hv : (fun i : Fin 2 => (Polynomial.aeval s) ((![1, Polynomial.X] : Fin 2 → Polynomial K) i)) =
      ![1,s] := by
    funext i
    fin_cases i <;> simp
  rw [hv]

/-- A nonzero binary form has a nonzero univariate dehomogenization
in the first coordinate chart, so any root there is algebraic. -/
theorem slope_isAlgebraic_of_homogeneous_binary_form_zero
    (p : MvPolynomial (Fin 2) K) (hp : p ≠ 0) {d : ℕ} (hh : p.IsHomogeneous d)
    (s : F) (hs : aeval ![(1 : F), s] p = 0) : IsAlgebraic K s := by
  let q : Polynomial K := aeval ![1, Polynomial.X] p
  have hq : q ≠ 0 := homogeneous_binary_first_chart_nonzero p hp hh
  exact ⟨q, hq, (eval_binary_first_chart p s).trans hs⟩

end DimensionFourDependence
