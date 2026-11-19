import DimensionFourDependence.ParabolaFromAffineSquare
import DimensionFourDependence.GraphBoundaryProportionality
import DimensionFourDependence.FullSourceDegree

/-! # Actual affine parabolas and lines in the original graph coordinates

The specified graph direction map is injective and linear. It preserves
independence of the two parabola directions, and the graph constant gives
the actual affine base point. All source-coordinate labels are retained.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

/-- The actual linear inclusion of projected directions into the
specified original four-coordinate graph hyperplane. -/
noncomputable def graphBoundaryDirectionLinearMap (p : Equiv.Perm (Fin 4)) (A : Fin 3 → L) :
    (Fin 3 → L) →ₗ[L] (Fin 4 → L) where
  toFun b := graphBoundaryDirection p A b
  map_add' b c := by
    funext j
    obtain ⟨i, rfl⟩ := p.surjective j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · change graphBoundaryDirection p A (b + c) (p 3) =
        graphBoundaryDirection p A b (p 3) + graphBoundaryDirection p A c (p 3)
      simp only [graphBoundaryDirection_last, dotProduct_add]
    · simp only [graphBoundaryDirection_first, Pi.add_apply]
  map_smul' s b := by
    funext j
    obtain ⟨i, rfl⟩ := p.surjective j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · change graphBoundaryDirection p A (s • b) (p 3) = s * graphBoundaryDirection p A b (p 3)
      simp only [graphBoundaryDirection_last, dotProduct_smul, smul_eq_mul]
    · simp only [graphBoundaryDirection_first, Pi.smul_apply, RingHom.id_apply]

/-- The original first-three coordinates give an actual left inverse
on graph directions, so the original graph inclusion is injective. -/
theorem graphBoundaryDirectionLinearMap_injective (p : Equiv.Perm (Fin 4)) (A : Fin 3 → L) :
    Function.Injective (graphBoundaryDirectionLinearMap p A) := by
  intro b c he
  funext i
  have hi := congrFun he (p i.castSucc)
  exact (graphBoundaryDirection_first p A b i).symm.trans
    (hi.trans (graphBoundaryDirection_first p A c i))

/-- An actual quadratic expression in the projected point gives
the actual quadratic expression in all four original graph coordinates. -/
theorem actual_graph_point_quadratic_expression
    (p : Equiv.Perm (Fin 4)) (k : L) (A a b c : Fin 3 → L)
    (x : Fin 4 → F) (y : Fin 3 → F) (hx : x ∘ p = affineGraphPoint k A y)
    (t : F) (hy : ∀ i, y i = algebraMap L F (a i) + algebraMap L F (b i) * t +
      algebraMap L F (c i) * t ^ 2) :
    ∀ j, x j = algebraMap L F (sourceGraphPoint p k A a j) +
      algebraMap L F (graphBoundaryDirection p A b j) * t +
      algebraMap L F (graphBoundaryDirection p A c j) * t ^ 2 := by
  intro j
  obtain ⟨i, rfl⟩ := p.surjective j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · change x (p 3) = algebraMap L F (sourceGraphPoint p k A a (p 3)) +
      algebraMap L F (graphBoundaryDirection p A b (p 3)) * t +
      algebraMap L F (graphBoundaryDirection p A c (p 3)) * t ^ 2
    have hlast : x (p 3) = algebraMap L F k + ∑ i, algebraMap L F (A i) * y i := by
      have he := congrFun hx (Fin.last 3)
      rw [show (Fin.last 3 : Fin 4) = 3 from by decide] at he
      change x (p 3) = algebraMap L F k + ∑ i, algebraMap L F (A i) * y i at he
      exact he
    have hbase : sourceGraphPoint p k A a (p 3) = k + ∑ i, A i * a i := by
      simp only [sourceGraphPoint, Function.comp_apply, Equiv.symm_apply_apply, affineGraphPoint,
        Algebra.algebraMap_self, RingHom.id_apply]
      exact @Fin.snoc_last 3 (fun _ => L) (k + ∑ i, A i * a i) a
    have hterm (i : Fin 3) : algebraMap L F (A i) * y i =
        algebraMap L F (A i * a i) + algebraMap L F (A i * b i) * t +
          algebraMap L F (A i * c i) * t ^ 2 := by
      rw [hy i, map_mul, map_mul, map_mul]
      ring
    rw [hlast, graphBoundaryDirection_last, graphBoundaryDirection_last, hbase]
    simp only [hterm, map_add, map_sum, dotProduct, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  · have hfirst := congrFun hx i.castSucc
    simp only [Function.comp_apply, affineGraphPoint, Fin.snoc_castSucc] at hfirst
    rw [hfirst, graphBoundaryDirection_first, graphBoundaryDirection_first]
    simpa only [sourceGraphPoint, Function.comp_apply, Equiv.symm_apply_apply,
      affineGraphPoint, Fin.snoc_castSucc] using hy i

/-- An actual affine line in the projected graph coordinates would
be an actual affine line in the original four source coordinates. -/
theorem actual_graph_line_of_projected_line
    (p : Equiv.Perm (Fin 4)) (k : L) (A : Fin 3 → L)
    (x : Fin 4 → F) (y : Fin 3 → F) (hx : x ∘ p = affineGraphPoint k A y)
    (hy : LiesInAffineLine (E := L) y) : LiesInAffineLine (E := L) x := by
  obtain ⟨a, b, hb, t, hexp⟩ := hy
  have hquadratic : ∀ i, y i = algebraMap L F (a i) + algebraMap L F (b i) * t +
      algebraMap L F ((0 : Fin 3 → L) i) * t ^ 2 := by simpa using hexp
  have he := actual_graph_point_quadratic_expression p k A a b 0 x y hx t hquadratic
  refine ⟨sourceGraphPoint p k A a, graphBoundaryDirection p A b,
    graphBoundaryDirection_ne_zero p A b hb, t, ?_⟩
  intro j
  have hz : graphBoundaryDirection p A (0 : Fin 3 → L) j = 0 :=
    congrFun (graphBoundaryDirectionLinearMap p A).map_zero j
  simpa only [hz, map_zero, zero_mul, add_zero] using he j

/-- A nondegenerate projected parabola remains a nondegenerate
parabola in the actual original four-coordinate graph hyperplane. -/
theorem actual_graph_parabola_of_projected_parabola
    (p : Equiv.Perm (Fin 4)) (k : L) (A : Fin 3 → L)
    (x : Fin 4 → F) (y : Fin 3 → F) (hx : x ∘ p = affineGraphPoint k A y)
    (hy : LiesInAffineParabola (L := L) y) : LiesInAffineParabola (L := L) x := by
  obtain ⟨a, b, c, hbc, t, ht, hexp⟩ := hy
  have hLI := hbc.map' (graphBoundaryDirectionLinearMap p A)
    (LinearMap.ker_eq_bot.mpr (graphBoundaryDirectionLinearMap_injective p A))
  refine ⟨sourceGraphPoint p k A a, graphBoundaryDirection p A b, graphBoundaryDirection p A c,
    ?_, t, ht, actual_graph_point_quadratic_expression p k A a b c x y hx t hexp⟩
  convert hLI using 1
  funext i
  fin_cases i <;> rfl

end DimensionFourDependence
