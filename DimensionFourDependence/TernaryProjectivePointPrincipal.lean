import DimensionFourDependence.ProjectivePointChartIdeal
import DimensionFourDependence.ProjectiveCovectorTranscendence

/-! # A nonconstant ternary projective point has a principal relation ideal

A transcendental original coordinate ratio gives a two-coordinate affine
chart with a principal relation prime. Homogenization and an explicit
coordinate permutation transport its whole ideal to the original three
coordinates. No hypersurface equation is assumed in this construction.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Two distinct original coordinates can be assigned the normalized
chart coordinate and its transcendental affine coordinate. -/
theorem exists_ternary_chart_order (i j : Fin 3) (hij : i ≠ j) :
    ∃ r : Fin 3 ≃ Option (Option Unit), r j = none ∧ r i = some (some ()) := by
  obtain ⟨p, hp0, hp2⟩ := exists_ternary_permutation_first_last i j hij
  let e : Fin 3 ≃ Option (Option Unit) := {
    toFun := ![some (some ()), some none, none]
    invFun := fun o => o.elim 2 (fun u => u.elim 1 (fun _ => 0))
    left_inv := by intro k; fin_cases k <;> rfl
    right_inv := by intro o; rcases o with _ | (_ | u); rfl; rfl; cases u; rfl }
  refine ⟨p.symm.trans e, ?_, ?_⟩
  · change e (p.symm j) = none
    rw [← hp2, Equiv.symm_apply_apply]
    rfl
  · change e (p.symm i) = some (some ())
    rw [← hp0, Equiv.symm_apply_apply]
    rfl

/-- A transcendental ratio constructs a homogeneous generator of
the entire original ternary projective relation prime. -/
theorem ternary_projective_point_exists_homogeneous_generator
    (A : Fin 3 → F) (i j : Fin 3) (hj : A j ≠ 0)
    (ht : Transcendental K (A i / A j)) :
    ∃ (Φ : MvPolynomial (Fin 3) K) (d : ℕ), Φ.IsHomogeneous d ∧
      (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ} := by
  have hij : i ≠ j := by
    intro he
    subst i
    apply ht
    rw [div_self hj]
    exact isAlgebraic_one
  obtain ⟨r, hrj, hri⟩ := exists_ternary_chart_order i j hij
  have hrj' : r.symm none = j := r.symm_apply_eq.mpr hrj.symm
  have hri' : r.symm (some (some ())) = i := r.symm_apply_eq.mpr hri.symm
  let x : Option Unit → F := fun k => A (r.symm (some k)) / A j
  obtain ⟨Q, d, hQ, hcone⟩ := two_coordinate_projective_closure_exists_homogeneous_generator
    (A i / A j) (x none) ht
  have hx : (fun k : Option Unit => k.elim (x none) (fun _ => A i / A j)) = x := by
    funext k
    rcases k with _ | u
    · rfl
    · cases u
      simp only [Option.elim_some, x, hri']
  rw [hx] at hcone
  refine ⟨rename r.symm Q, d, hQ.rename_isHomogeneous, ?_⟩
  rw [projectiveFieldPointIdeal_eq_chart_comap A r (by rwa [hrj']), hrj']
  change (projectiveConeIdeal (L := K) x).comap (renameEquiv K r).toRingHom = _
  rw [hcone]
  ext S
  change rename r S ∈ Ideal.span {Q} ↔ S ∈ Ideal.span {rename r.symm Q}
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  have he := map_dvd_iff (renameEquiv K r)
    (a := (renameEquiv K r).symm Q) (b := S)
  simp only [renameEquiv_symm, renameEquiv_apply, rename_rename,
    Equiv.self_comp_symm, rename_id_apply] at he
  exact he

/-- Positive dimension of the actual original projective ratio field
supplies the transcendental chart and hence the entire principal ideal. -/
theorem nonconstant_ternary_projective_point_exists_homogeneous_generator
    (A : Fin 3 → F) (j : Fin 3) (hj : A j ≠ 0)
    (hdim : Algebra.trdeg K (projectiveRatioField (K := K) A j) ≠ 0) :
    ∃ (Φ : MvPolynomial (Fin 3) K) (d : ℕ), Φ.IsHomogeneous d ∧
      (projectiveFieldPointIdeal (E := K) A).toIdeal = Ideal.span {Φ} := by
  obtain ⟨i, hi⟩ := projective_ratio_positive_dimension_exists_transcendental_coordinate A j hdim
  exact ternary_projective_point_exists_homogeneous_generator A i j hj hi

end DimensionFourDependence
