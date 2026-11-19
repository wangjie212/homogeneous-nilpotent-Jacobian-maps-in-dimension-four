import DimensionFourDependence.ProjectiveGraphIdealImage
import DimensionFourDependence.ProjectiveBoundaryProjection
import DimensionFourDependence.GraphHilbert
import DimensionFourDependence.InfinityChartHilbertBound

/-! # Original coordinate ordering in the actual infinity graph elimination

The entire closure ideal commutes with reindexing, coefficient extension
and graph elimination. Thus the actual original full-fiber single-support
statement and the actual projected local bound give the degree bound in
the original four coordinates, with no assumed coordinate comparison.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {E F G sigma tau : Type*} [Field E] [Field F] [Field G]
    [Algebra E F] [Algebra E G]

/-- Reindexing maps the entire original projective closure ideal
onto the entire reindexed closure ideal. -/
theorem projectiveConeIdeal_rename_map (e : sigma ≃ tau) (x : sigma → G) :
    (projectiveConeIdeal (L := E) x).map (rename (Option.map e)).toRingHom =
      projectiveConeIdeal (L := E) (x ∘ e.symm) := by
  have hcomap : projectiveConeIdeal (L := E) x =
      (projectiveConeIdeal (L := E) (x ∘ e.symm)).comap (rename (Option.map e)).toRingHom := by
    ext P
    change projectiveConeMap (L := E) x P = 0 ↔
      projectiveConeMap (L := E) (x ∘ e.symm) (rename (Option.map e) P) = 0
    rw [projectiveConeMap_coordinate_projection]
    have hx : (x ∘ e.symm) ∘ e = x := by funext i; simp
    rw [hx]
  rw [hcomap]
  exact Ideal.map_comap_of_surjective _ (renameEquiv E e.optionCongr).surjective _

/-- The same entire-ideal reindexing identity holds after extending
the coefficients by the specified original field homomorphism. -/
theorem extended_projectiveConeIdeal_rename_map (e : sigma ≃ tau) (x : sigma → G) :
    (Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x)).map
      (rename (Option.map e)).toRingHom =
      Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) (x ∘ e.symm)) := by
  rw [Ideal.map_map]
  have he : (rename (R := F) (Option.map e)).toRingHom.comp (MvPolynomial.map (algebraMap E F)) =
      (MvPolynomial.map (algebraMap E F)).comp (rename (R := E) (Option.map e)).toRingHom := by
    exact RingHom.ext (fun P => (MvPolynomial.map_rename (algebraMap E F) (Option.map e) P).symm)
  rw [he, ← Ideal.map_map, projectiveConeIdeal_rename_map]

/-- Reindexing preserves the exact original infinity-section ideal,
including its distinguished homogenizing-coordinate equation. -/
theorem extended_projectiveInfinityIdeal_rename_map (e : sigma ≃ tau) (x : sigma → G) :
    (Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ⊔
      Ideal.span ({X none} : Set (MvPolynomial (Option sigma) F))).map
        (rename (Option.map e)).toRingHom =
      Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) (x ∘ e.symm)) ⊔
        Ideal.span ({X none} : Set (MvPolynomial (Option tau) F)) := by
  rw [Ideal.map_sup, extended_projectiveConeIdeal_rename_map, Ideal.map_span, Set.image_singleton]
  change _ ⊔ Ideal.span ({rename (Option.map e) (X none)} : Set _) = _
  simp only [rename_X, Option.map_none]

/-- The specified original permutation followed by the actual graph
hyperplane pullback. -/
noncomputable def reindexedProjectiveGraphPullback {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (c : F) (a : Fin n → F) :
    MvPolynomial (Option (Fin (n + 1))) F →ₐ[F] MvPolynomial (Option (Fin n)) F :=
  (projectiveGraphPullback c a).comp (rename (Option.map p.symm))

/-- The actual reordered graph substitution preserves every homogeneous degree. -/
theorem reindexedProjectiveGraphPullback_homogeneous {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (c : F) (a : Fin n → F)
    (P : MvPolynomial (Option (Fin (n + 1))) F) {d : ℕ} (hP : P.IsHomogeneous d) :
    (reindexedProjectiveGraphPullback p c a P).IsHomogeneous d :=
  projectiveGraphPullback_isHomogeneous c a hP.rename_isHomogeneous

/-- The actual reordered graph substitution is onto the whole target ring. -/
theorem reindexedProjectiveGraphPullback_surjective {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (c : F) (a : Fin n → F) :
    Function.Surjective (reindexedProjectiveGraphPullback p c a) :=
  (projectiveGraphPullback_surjective c a).comp (renameEquiv F p.symm.optionCongr).surjective

/-- The actual reordered graph substitution is onto each homogeneous piece. -/
theorem reindexedProjectiveGraphPullback_homogeneous_surjective {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (c : F) (a : Fin n → F) (d : ℕ) :
    Function.Surjective (homogeneousPolynomialAlgebraMap (reindexedProjectiveGraphPullback p c a)
      (fun _ P hP => reindexedProjectiveGraphPullback_homogeneous p c a P hP) d) :=
  homogeneousPolynomialAlgebraMap_surjective_comp
    (rename (Option.map p.symm)) (fun _ _ hP => hP.rename_isHomogeneous)
    (projectiveGraphPullback c a) (fun _ _ hP => projectiveGraphPullback_isHomogeneous c a hP)
    (fun d => (homogeneousRenameEquiv (L := F) p.symm.optionCongr d).surjective)
    (projectiveGraphPullback_homogeneous_surjective c a) d

/-- For an original full point with the actual graph equation, the
whole extended infinity ideal maps to the projected infinity ideal. -/
theorem extended_projectiveInfinityIdeal_reindexed_graph_map {n : ℕ}
    (p : Equiv.Perm (Fin (n + 1))) (c : E) (a : Fin n → E)
    (x : Fin (n + 1) → G) (y : Fin n → G) (hx : x ∘ p = affineGraphPoint c a y) :
    (Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ⊔
      Ideal.span ({X none} : Set (MvPolynomial (Option (Fin (n + 1))) F))).map
        (reindexedProjectiveGraphPullback p (algebraMap E F c)
          (fun i => algebraMap E F (a i))).toRingHom =
      Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) y) ⊔
        Ideal.span ({X none} : Set (MvPolynomial (Option (Fin n)) F)) := by
  change Ideal.map ((projectiveGraphPullback (algebraMap E F c)
    (fun i => algebraMap E F (a i))).toRingHom.comp (rename (Option.map p.symm)).toRingHom) _ = _
  rw [← Ideal.map_map, extended_projectiveInfinityIdeal_rename_map]
  change Ideal.map _ (Ideal.map (MvPolynomial.map (algebraMap E F))
    (projectiveConeIdeal (L := E) (x ∘ p)) ⊔ Ideal.span {X none}) = _
  rw [hx, extended_projectiveInfinityIdeal_graph_map]

/-- The original full curve has degree at most two from its actual
single-support infinity section and its constructed projected local chart. -/
theorem original_curve_degree_le_two_of_graph_infinity_local_bound
    (p : Equiv.Perm (Fin 4)) (c : E) (a : Fin 3 → E)
    (x : Fin 4 → G) (y : Fin 3 → G) (hx : x ∘ p = affineGraphPoint c a y)
    {e : ℕ} (he : HasCurveHilbertDegree (projectiveConeIdeal (L := E) x) e)
    (s0 : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) F))
    (hsupport : ∀ s : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) F),
      Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ⊔
        Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 4)) F)) ≤ s.asHomogeneousIdeal.toIdeal → s = s0)
    (b w z : Fin 3 → F) (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0)
    (hlocal : HasOriginLocalLengthAtMostTwo (extendedProjectiveInfinityChartIdeal (E := E) y b w z)) :
    e ≤ 2 := by
  have hreindex := (curveHilbertDegree_reindex (L := E) p x e).mpr he
  rw [hx] at hreindex
  have hprojected := (curveHilbertDegree_graph c a y e).mp hreindex
  exact curve_hilbert_degree_le_two_of_single_support_infinity_chart y hprojected _
    (reindexedProjectiveGraphPullback p (algebraMap E F c) (fun i => algebraMap E F (a i)))
    (fun _ P hP => reindexedProjectiveGraphPullback_homogeneous p _ _ P hP)
    (reindexedProjectiveGraphPullback_surjective p _ _)
    (reindexedProjectiveGraphPullback_homogeneous_surjective p _ _)
    (extended_projectiveInfinityIdeal_reindexed_graph_map p c a x y hx)
    s0 hsupport b w z hdet hlocal

end DimensionFourDependence
