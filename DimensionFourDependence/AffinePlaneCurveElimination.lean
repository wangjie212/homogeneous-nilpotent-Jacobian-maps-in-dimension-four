import DimensionFourDependence.AffineHyperplane
import DimensionFourDependence.AffineSubstitutionDegree
import DimensionFourDependence.CommutativePolynomialChainRule
import DimensionFourDependence.ProjectiveFiberEquations

/-! # Eliminate a verified affine plane before restricting its quadratic equation -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 3900000

variable {E F : Type u} [Field E] [Field F] [Algebra E F]
local notation "R₂" => MvPolynomial (Fin 2) E
local notation "R₃" => MvPolynomial (Fin 3) E

/-- Eliminating the normalized affine plane produces a nonzero equation
of degree at most two. Independence of the full actual gradients prevents
the restriction of the second equation from vanishing identically. -/
theorem normalized_affine_plane_restricts_quadric_to_nonzero_binary_equation
    (y : Fin 3 → F) (P Q : R₃) (hp : P.totalDegree ≤ 1) (hq : Q.totalDegree ≤ 2)
    (hlast : pderiv (Fin.last 2) P = 1) (hP : aeval y P = 0) (hQ : aeval y Q = 0)
    (hind : ∀ a b : F, a • (fun i => aeval y (pderiv i Q)) + b • (fun i => aeval y (pderiv i P)) = 0 →
      a = 0 ∧ b = 0) :
    ∃ v : Fin 3 → R₂, (∀ i : Fin 2, v i.castSucc = X i) ∧ (∀ i, (v i).totalDegree ≤ 1) ∧
      (∀ i, aeval (fun j : Fin 2 => y j.castSucc) (v i) = y i) ∧
      aeval v Q ≠ 0 ∧ (aeval v Q).totalDegree ≤ 2 ∧ aeval (fun j : Fin 2 => y j.castSucc) (aeval v Q) = 0 := by
  classical
  let x : Fin 2 → F := fun i => y i.castSucc
  let b : Fin 2 → E := fun i => (pderiv i.castSucc P).coeff 0
  let T : R₂ := -C (P.coeff 0) - linearFormPolynomial b
  let v : Fin 3 → R₂ := Fin.lastCases T (fun i => X (R := E) i)
  have hVlast : v (Fin.last 2) = T := Fin.lastCases_last
  have hVcast (i : Fin 2) : v i.castSucc = X i := by simp [v]
  have hFit (j : Fin 3) : aeval x (v j) = y j := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [hVlast]
      have he := affine_hyperplane_solve_last P hp hlast y hP
      simpa only [T, b, x, linearFormPolynomial, map_sub, map_neg, map_sum, map_mul, aeval_C, aeval_X] using he.symm
    · rw [hVcast, aeval_X]
  have hComp (U : R₃) : aeval x (aeval v U) = aeval y U := by
    rw [comp_aeval_apply v (aeval x : R₂ →ₐ[E] F), show (fun j => aeval x (v j)) = y from funext hFit]
  have hv (j : Fin 3) : (v j).totalDegree ≤ 1 := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [hVlast]
      exact (totalDegree_sub _ _).trans (max_le (by simp) (linearFormPolynomial_totalDegree _))
    · rw [hVcast, totalDegree_X]
  have hdT (i : Fin 2) : pderiv i T = -C (b i) := by
    change pderiv i (-C (P.coeff 0) - linearFormPolynomial b) = _
    rw [map_sub, map_neg, pderiv_C, neg_zero, linearFormPolynomial_pderiv, zero_sub]
  let A : R₂ := aeval v Q
  have hA : A ≠ 0 := by
    intro hz
    have hDep (i : Fin 2) : aeval y (pderiv i.castSucc Q) -
        aeval y (pderiv (Fin.last 2) Q) * algebraMap E F (b i) = 0 := by
      have hD := derivation_commutative_aeval_chain_rule (pderiv (R := E) i) v Q
      rw [Fin.sum_univ_castSucc] at hD
      simp only [hVcast, hVlast] at hD
      have hAz : aeval v Q = 0 := hz
      have hsum : (∑ j : Fin 2, aeval v (pderiv j.castSucc Q) * pderiv i (X j)) =
          aeval v (pderiv i.castSucc Q) := by simp [Pi.single_apply]
      rw [hAz, map_zero, hsum, hdT] at hD
      have he := congrArg (aeval x : R₂ →ₐ[E] F) hD
      simp only [map_zero, map_add, map_mul, map_neg, aeval_C, hComp] at he
      linear_combination -he
    have hz : (1 : F) • (fun i => aeval y (pderiv i Q)) +
        (-aeval y (pderiv (Fin.last 2) Q)) • (fun i => aeval y (pderiv i P)) = 0 := by
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, one_smul, smul_eq_mul]
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [hlast, map_one, mul_one, add_neg_cancel]
      · rw [affine_pderiv_eq_C P hp, aeval_C]
        linear_combination hDep i
    exact one_ne_zero (hind _ _ hz).1
  exact ⟨v, hVcast, hv, hFit, hA,
    (totalDegree_aeval_le_of_affine v hv Q).trans hq, (hComp Q).trans hQ⟩

/-- An arbitrary affine plane with an independent quadratic equation
admits the same elimination in a permutation of the original coordinates. -/
theorem affine_plane_restricts_quadric_to_nonzero_binary_equation
    (y : Fin 3 → F) (P Q : R₃) (hp : P.totalDegree ≤ 1) (hq : Q.totalDegree ≤ 2)
    (hP : aeval y P = 0) (hQ : aeval y Q = 0)
    (hind : ∀ a b : F, a • (fun i => aeval y (pderiv i Q)) + b • (fun i => aeval y (pderiv i P)) = 0 →
      a = 0 ∧ b = 0) :
    ∃ (e : Equiv.Perm (Fin 3)) (v : Fin 3 → R₂) (B : R₂),
      (∀ i : Fin 2, v i.castSucc = X i) ∧ (∀ i, (v i).totalDegree ≤ 1) ∧
      (∀ i, aeval (fun j : Fin 2 => y (e j.castSucc)) (v i) = y (e i)) ∧
      B ≠ 0 ∧ B.totalDegree ≤ 2 ∧ aeval (fun j : Fin 2 => y (e j.castSucc)) B = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, (pderiv i P).coeff 0 ≠ 0 := by
    by_contra! h
    have he : (0 : F) • (fun i => aeval y (pderiv i Q)) +
        (1 : F) • (fun i => aeval y (pderiv i P)) = 0 := by
      funext j
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, zero_smul, one_smul, zero_add,
        affine_pderiv_eq_C _ hp, h, map_zero, map_zero]
      rfl
    exact one_ne_zero (hind 0 1 he).2
  let e : Equiv.Perm (Fin 3) := Equiv.swap i (Fin.last 2)
  let z := y ∘ e
  let a := (pderiv i P).coeff 0
  let P' := C a⁻¹ * rename e P
  let Q' := rename e Q
  have he (i : Fin 3) : e (e i) = i := Equiv.swap_apply_self _ _ _
  have hEval (T : R₃) : aeval z (rename e T) = aeval y T := by
    rw [aeval_rename]
    exact congrArg (fun g : Fin 3 → F => aeval g T) (funext fun i => congrArg y (he i))
  have hp' : P'.totalDegree ≤ 1 := by
    change (C a⁻¹ * rename e P).totalDegree ≤ 1
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, zero_add]
    exact (totalDegree_rename_le _ _).trans hp
  have hq' : Q'.totalDegree ≤ 2 := (totalDegree_rename_le _ _).trans hq
  have hP' : aeval z P' = 0 := by
    change aeval z (C a⁻¹ * rename e P) = _
    rw [map_mul, hEval, hP, mul_zero]
  have hQ' : aeval z Q' = 0 := (hEval Q).trans hQ
  have hElim (j : Fin 3) (T : R₃) :
      aeval z (pderiv (e j) (rename e T)) = aeval y (pderiv j T) := by
    rw [pderiv_rename e.injective, hEval]
  have hlast : pderiv (Fin.last 2) P' = 1 := by
    have hei : e i = Fin.last 2 := Equiv.swap_apply_left _ _
    change pderiv (Fin.last 2) (C a⁻¹ * rename e P) = _
    rw [pderiv_C_mul, ← hei, pderiv_rename e.injective, affine_pderiv_eq_C _ hp,
      rename_C, ← map_mul, inv_mul_cancel₀ hi, map_one]
  have hi' : ∀ u w : F, u • (fun j => aeval z (pderiv j Q')) + w • (fun j => aeval z (pderiv j P')) = 0 →
      u = 0 ∧ w = 0 := by
    intro u w hw
    let c := algebraMap E F a⁻¹
    have hc : c ≠ 0 := fun hz => (inv_ne_zero hi) ((algebraMap E F).injective (hz.trans (map_zero _).symm))
    have hydro : u • (fun j => aeval y (pderiv j Q)) + (w * c) • (fun j => aeval y (pderiv j P)) = 0 := by
      funext j
      have h := congrFun hw (e j)
      change u * aeval z (pderiv (e j) (rename e Q)) + w *
        aeval z (pderiv (e j) (C a⁻¹ * rename e P)) = 0 at h
      rw [pderiv_C_mul, map_mul, aeval_C, hElim, hElim] at h
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, c, mul_assoc] using h
    obtain ⟨hu, hw'⟩ := hind u (w * c) hydro
    exact ⟨hu, (mul_eq_zero.mp hw').resolve_right hc⟩
  obtain ⟨v, hV, hDegree, hFit, hNe, hBound, hZero⟩ :=
    normalized_affine_plane_restricts_quadric_to_nonzero_binary_equation z P' Q' hp' hq' hlast hP' hQ' hi'
  exact ⟨e, v, aeval v Q', hV, hDegree, hFit, hNe, hBound, hZero⟩

end DimensionFourDependence
