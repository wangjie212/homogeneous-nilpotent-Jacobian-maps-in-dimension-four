import DimensionFourDependence.HomogeneousDehomogenize

/-! # Exact dehomogenization and homogenization in the final coordinate -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] {n : ℕ}

/-- Set the final source coordinate to one, retaining the original
ordering of all the active coordinates. -/
noncomputable def lastCoordinateDehomogenize :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (Fin.lastCases 1 X)

theorem lastCoordinateDehomogenize_C (c : K) :
    lastCoordinateDehomogenize (C c : MvPolynomial (Fin (n + 1)) K) = C c := by
  simp [lastCoordinateDehomogenize]

theorem lastCoordinateDehomogenize_X_last :
    lastCoordinateDehomogenize (X (Fin.last n) : MvPolynomial (Fin (n + 1)) K) = 1 := by
  simp [lastCoordinateDehomogenize]

theorem lastCoordinateDehomogenize_X_castSucc (i : Fin n) :
    lastCoordinateDehomogenize (X i.castSucc : MvPolynomial (Fin (n + 1)) K) = X i := by
  simp [lastCoordinateDehomogenize]

/-- The final-coordinate chart is exactly the coordinate-free
projective chart, with its indices explicitly reidentified. -/
theorem lastCoordinateDehomogenize_eq_projective_chart
    (P : MvPolynomial (Fin (n + 1)) K) :
    lastCoordinateDehomogenize P =
      projectiveDehomogenize (rename finSuccEquivLast P) := by
  have he : (lastCoordinateDehomogenize (K := K) (n := n)) =
      (projectiveDehomogenize (R := K)).comp (rename finSuccEquivLast) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [AlgHom.comp_apply, lastCoordinateDehomogenize_X_last,
        projectiveDehomogenize_X_none]
    · simp [AlgHom.comp_apply, lastCoordinateDehomogenize_X_castSucc,
        projectiveDehomogenize_X_some]
  exact AlgHom.congr_fun he P

/-- Dehomogenization commutes with each active derivative. -/
theorem lastCoordinateDehomogenize_pderiv
    (P : MvPolynomial (Fin (n + 1)) K) (i : Fin n) :
    lastCoordinateDehomogenize (pderiv i.castSucc P) =
      pderiv i (lastCoordinateDehomogenize P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [lastCoordinateDehomogenize]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [pderiv_X, Pi.single_apply, hP, apply_ite,
        lastCoordinateDehomogenize_X_last]
    · simp [pderiv_X, Pi.single_apply, hP, apply_ite,
        lastCoordinateDehomogenize_X_castSucc, Fin.castSucc_inj]

/-- The chart cannot increase total degree. -/
theorem lastCoordinateDehomogenize_totalDegree
    (P : MvPolynomial (Fin (n + 1)) K) :
    (lastCoordinateDehomogenize P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_aeval_le_of_linear
  intro i
  exact Fin.lastCases (by simp) (fun i => by simp) i

/-- Homogenize in the actual final coordinate, leaving the active
coordinate order unchanged. -/
noncomputable def lastCoordinateHomogenize
    (P : MvPolynomial (Fin n) K) (d : ℕ) : MvPolynomial (Fin (n + 1)) K :=
  rename finSuccEquivLast.symm (projectiveHomogenize P d)

theorem lastCoordinateHomogenize_isHomogeneous
    (P : MvPolynomial (Fin n) K) (d : ℕ) (hd : P.totalDegree ≤ d) :
    (lastCoordinateHomogenize P d).IsHomogeneous d :=
  (projectiveHomogenize_isHomogeneous P d hd).rename_isHomogeneous

theorem lastCoordinateDehomogenize_homogenize
    (P : MvPolynomial (Fin n) K) (d : ℕ) :
    lastCoordinateDehomogenize (lastCoordinateHomogenize P d) = P := by
  rw [lastCoordinateDehomogenize_eq_projective_chart, lastCoordinateHomogenize]
  simpa only [rename_rename, Equiv.self_comp_symm, rename_id, AlgHom.id_apply] using
    projectiveDehomogenize_homogenize P d

/-- The entire homogeneous form, including powers of the fixed
coordinate, is recovered from the chart in its prescribed degree. -/
theorem lastCoordinateHomogenize_dehomogenize
    (P : MvPolynomial (Fin (n + 1)) K) {d : ℕ} (hP : P.IsHomogeneous d) :
    lastCoordinateHomogenize (lastCoordinateDehomogenize P) d = P := by
  rw [lastCoordinateHomogenize, lastCoordinateDehomogenize_eq_projective_chart,
    homogeneous_homogenize_dehomogenize _ hP.rename_isHomogeneous]
  simp only [rename_rename, Equiv.symm_comp_self, rename_id, AlgHom.id_apply]

/-- Equal final-coordinate charts determine forms of the same degree. -/
theorem lastCoordinateDehomogenize_injective_on_homogeneous_degree
    (P Q : MvPolynomial (Fin (n + 1)) K) {d : ℕ}
    (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous d)
    (he : lastCoordinateDehomogenize P = lastCoordinateDehomogenize Q) : P = Q := by
  rw [← lastCoordinateHomogenize_dehomogenize P hP,
    ← lastCoordinateHomogenize_dehomogenize Q hQ, he]

/-- Removing the value at the active origin leaves precisely one
elementary target translation times the final-coordinate power. -/
theorem homogeneous_form_reconstructs_normalized_final_coordinate_chart
    (P : MvPolynomial (Fin (n + 1)) K) {d : ℕ} (hP : P.IsHomogeneous d) :
    let b := lastCoordinateDehomogenize P
    let c := aeval (fun _ : Fin n => (0 : K)) b
    (b - C c).totalDegree ≤ d ∧
      aeval (fun _ : Fin n => (0 : K)) (b - C c) = 0 ∧
      P = lastCoordinateHomogenize (b - C c) d + C c * X (Fin.last n) ^ d := by
  dsimp only
  let b := lastCoordinateDehomogenize P
  let c := aeval (fun _ : Fin n => (0 : K)) b
  have hb : b.totalDegree ≤ d := by
    by_cases hz : P = 0
    · simp [b, hz]
    · exact (lastCoordinateDehomogenize_totalDegree P).trans (hP.totalDegree hz).le
  have hbn : (b - C c).totalDegree ≤ d :=
    (totalDegree_sub _ _).trans (max_le hb (by simp))
  refine ⟨hbn, by simp [b, c], ?_⟩
  apply lastCoordinateDehomogenize_injective_on_homogeneous_degree _ _ hP
    ((lastCoordinateHomogenize_isHomogeneous _ d hbn).add
      ((isHomogeneous_X_pow (Fin.last n) d).C_mul c))
  simp only [map_add, lastCoordinateDehomogenize_homogenize, map_mul,
    lastCoordinateDehomogenize_C, map_pow, lastCoordinateDehomogenize_X_last, one_pow, mul_one]
  exact (sub_add_cancel b (C c)).symm

end DimensionFourDependence
