import DimensionFourDependence.ProjectiveGraph
import DimensionFourDependence.HilbertFieldExtension
import DimensionFourDependence.GradedSurjectiveHilbertTransport

/-! # The entire original closure ideal under graph elimination

The homogeneous graph pullback maps the original full closure ideal
onto the projected closure ideal. This equality remains exact after a
specified coefficient extension and after adding the infinity equation.
It is an identity of the entire ideals, not only the displayed low-degree
equations or their sets of geometric points.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {E F G : Type*} [Field E] [Field F] [Field G]
    [Algebra E F] [Algebra E G] {n : ℕ}

/-- Graph substitution is onto the whole original polynomial ring. -/
theorem projectiveGraphPullback_surjective (c : E) (a : Fin n → E) :
    Function.Surjective (projectiveGraphPullback c a) :=
  fun P => ⟨rename (Option.map Fin.castSucc) P, projectiveGraphPullback_rename c a P⟩

/-- Graph substitution is onto every specified homogeneous piece. -/
theorem projectiveGraphPullback_homogeneous_surjective (c : E) (a : Fin n → E) (d : ℕ) :
    Function.Surjective (homogeneousPolynomialAlgebraMap (projectiveGraphPullback c a)
      (fun _ _ hP => projectiveGraphPullback_isHomogeneous c a hP) d) :=
  homogeneousGraphPullback_surjective c a d

/-- The entire original cone map factors through the actual graph
hyperplane, retaining all polynomial relations and their grading. -/
theorem projectiveConeMap_graph (c : E) (a : Fin n → E) (x : Fin n → G) :
    projectiveConeMap (L := E) (affineGraphPoint c a x) =
      (projectiveConeMap (L := E) x).comp (projectiveGraphPullback c a) := by
  apply MvPolynomial.algHom_ext
  intro j
  cases j with
  | none => simp [projectiveConeMap_X, projectiveGraphPullback_X_none]
  | some j =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [projectiveGraphPullback_X_last, projectiveConeMap_X, projectiveGraphLinear,
        affineGraphPoint, Finset.sum_mul, add_mul, mul_assoc]
    · simp [projectiveGraphPullback_X_castSucc, projectiveConeMap_X, affineGraphPoint]

/-- The whole actual full graph closure prime is the preimage of the
whole actual projected closure prime. -/
theorem projectiveConeIdeal_graph_comap (c : E) (a : Fin n → E) (x : Fin n → G) :
    projectiveConeIdeal (L := E) (affineGraphPoint c a x) =
      (projectiveConeIdeal (L := E) x).comap (projectiveGraphPullback c a).toRingHom := by
  ext P
  change projectiveConeMap (L := E) (affineGraphPoint c a x) P = 0 ↔
    projectiveConeMap (L := E) x (projectiveGraphPullback c a P) = 0
  rw [projectiveConeMap_graph]
  rfl

/-- Graph elimination maps the entire actual full closure ideal
onto the actual projected closure ideal. -/
theorem projectiveConeIdeal_graph_map (c : E) (a : Fin n → E) (x : Fin n → G) :
    (projectiveConeIdeal (L := E) (affineGraphPoint c a x)).map
      (projectiveGraphPullback c a).toRingHom = projectiveConeIdeal (L := E) x := by
  rw [projectiveConeIdeal_graph_comap]
  exact Ideal.map_comap_of_surjective _ (projectiveGraphPullback_surjective c a) _

/-- The original graph substitution commutes with the specified
coefficient extension, including its original affine constant. -/
theorem projectiveGraphPullback_map_coefficients (c : E) (a : Fin n → E)
    (P : MvPolynomial (Option (Fin (n + 1))) E) :
    projectiveGraphPullback (algebraMap E F c) (fun i => algebraMap E F (a i))
      (MvPolynomial.map (algebraMap E F) P) =
      MvPolynomial.map (algebraMap E F) (projectiveGraphPullback c a P) := by
  have he :
      (projectiveGraphPullback (algebraMap E F c) (fun i => algebraMap E F (a i))).toRingHom.comp
        (MvPolynomial.map (algebraMap E F)) =
      (MvPolynomial.map (algebraMap E F)).comp (projectiveGraphPullback c a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro j
      cases j with
      | none => simp [projectiveGraphPullback_X_none]
      | some j =>
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp [projectiveGraphPullback_X_last, projectiveGraphLinear]
        · simp [projectiveGraphPullback_X_castSucc]
  exact DFunLike.congr_fun he P

/-- Coefficient extension preserves the exact image equality of the
original full and projected closure ideals under graph elimination. -/
theorem extended_projectiveConeIdeal_graph_map (c : E) (a : Fin n → E) (x : Fin n → G) :
    (Ideal.map (MvPolynomial.map (algebraMap E F))
      (projectiveConeIdeal (L := E) (affineGraphPoint c a x))).map
        (projectiveGraphPullback (algebraMap E F c) (fun i => algebraMap E F (a i))).toRingHom =
      Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) := by
  rw [Ideal.map_map]
  have he :
      (projectiveGraphPullback (algebraMap E F c) (fun i => algebraMap E F (a i))).toRingHom.comp
        (MvPolynomial.map (algebraMap E F)) =
      (MvPolynomial.map (algebraMap E F)).comp (projectiveGraphPullback c a).toRingHom := by
    exact RingHom.ext (projectiveGraphPullback_map_coefficients c a)
  rw [he, ← Ideal.map_map, projectiveConeIdeal_graph_map]

/-- The original full infinity-section ideal maps exactly onto the
projected infinity-section ideal after the specified coefficient extension. -/
theorem extended_projectiveInfinityIdeal_graph_map (c : E) (a : Fin n → E) (x : Fin n → G) :
    (Ideal.map (MvPolynomial.map (algebraMap E F))
        (projectiveConeIdeal (L := E) (affineGraphPoint c a x)) ⊔
      Ideal.span ({X none} : Set (MvPolynomial (Option (Fin (n + 1))) F))).map
        (projectiveGraphPullback (algebraMap E F c) (fun i => algebraMap E F (a i))).toRingHom =
      Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ⊔
        Ideal.span ({X none} : Set (MvPolynomial (Option (Fin n)) F)) := by
  rw [Ideal.map_sup, extended_projectiveConeIdeal_graph_map, Ideal.map_span]
  simp only [Set.image_singleton]
  change _ ⊔ Ideal.span ({projectiveGraphPullback (algebraMap E F c)
    (fun i => algebraMap E F (a i)) (X none)} : Set _) = _
  rw [projectiveGraphPullback_X_none]

end DimensionFourDependence
