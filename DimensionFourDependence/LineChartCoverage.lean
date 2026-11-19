import DimensionFourDependence.LineChartPivots

/-! # Every projective line occurs in a matrix chart

A basis of the two-dimensional line has a nonzero coordinate minor.
Projection to those two coordinates is an isomorphism. After putting
the pivots first, the line is a graph. Thus coordinate-permuted matrix
charts cover all projective lines, without an assumed chart choice.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F : Type*} [Field F]

/-- Every two-dimensional subspace admits a bijective two-coordinate projection. -/
theorem projective_line_exists_bijective_pivot
    (L : Submodule F (Fin 4 → F)) (hL : finrank F L = 2) :
    ∃ p : Equiv.Perm (Fin 4), Function.Bijective ((linePivotProjection p).comp L.subtype) := by
  let b := Module.finBasisOfFinrankEq F L hL
  let u : Fin 4 → F := b 0
  let v : Fin 4 → F := b 1
  have hli : LinearIndependent F ![u, v] := by
    have hb := b.linearIndependent.map' L.subtype (by simp)
    have heq : L.subtype ∘ b = ![u, v] := by
      funext i
      fin_cases i <;> rfl
    rw [heq] at hb
    exact hb
  obtain ⟨i, j, hminor⟩ := independent_pair_exists_nonzero_coordinate_minor u v hli
  have hij : i ≠ j := by
    intro he
    subst j
    simp at hminor
  obtain ⟨p, hp0, hp1⟩ := exists_permutation_first_two i j hij
  let f := (linePivotProjection (F := F) p).comp L.subtype
  have hproj : LinearIndependent F ![f (b 0), f (b 1)] := by
    change LinearIndependent F ![![u (p 0), u (p 1)], ![v (p 0), v (p 1)]]
    rw [hp0, hp1]
    exact independent_pair_of_coordinate_minor (u i) (v i) (u j) (v j) hminor
  have hspan : Submodule.span F (Set.range ![f (b 0), f (b 1)]) = ⊤ := by
    apply Submodule.eq_top_iff_finrank_eq.mpr
    simpa only [Module.finrank_pi, Fintype.card_fin] using finrank_span_eq_card hproj
  have hle : Submodule.span F (Set.range ![f (b 0), f (b 1)]) ≤ LinearMap.range f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact ⟨b 0, rfl⟩
    · exact ⟨b 1, rfl⟩
  have hrange : LinearMap.range f = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact hle
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp hrange
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa only [Module.finrank_pi, Fintype.card_fin] using hL)).mpr hsurj
  exact ⟨p, hinj, hsurj⟩

/-- The coordinate-permuted matrix charts cover every projective line. -/
theorem projective_line_exists_graph_chart (L : Submodule F (Fin 4 → F)) (hL : finrank F L = 2) :
    ∃ (p : Equiv.Perm (Fin 4)) (B : Matrix (Fin 2) (Fin 2) F),
      L.map (lineCoordinatePermutation p).toLinearMap = graphLineFour B := by
  obtain ⟨p, hπ⟩ := projective_line_exists_bijective_pivot L hL
  let e := (lineCoordinatePermutation (F := F) p).trans fourCoordinateEquiv.symm
  let G := L.map e.toLinearMap
  have hcomp : (Prod.fst ∘ G.subtype) ∘ (e.submoduleMap L) =
      (linePivotProjection p).comp L.subtype := by
    funext x
    rfl
  have hbij : Function.Bijective (Prod.fst ∘ G.subtype) := by
    apply (Function.Bijective.of_comp_iff _ (e.submoduleMap L).bijective).mp
    rw [hcomp]
    exact hπ
  obtain ⟨f, hf⟩ := Submodule.exists_eq_graph hbij
  let B := LinearMap.toMatrix' f
  have hG : G = graphLine B := by
    simpa only [graphLine, B, Matrix.toLin'_toMatrix'] using hf
  have heq := congrArg (fun Q : Submodule F ((Fin 2 → F) × (Fin 2 → F)) =>
    Q.map (fourCoordinateEquiv (F := F)).toLinearMap) hG
  have hmaps : (fourCoordinateEquiv (F := F)).toLinearMap.comp e.toLinearMap =
      (lineCoordinatePermutation p).toLinearMap := by
    ext x i
    simp [e]
  change (L.map e.toLinearMap).map (fourCoordinateEquiv (F := F)).toLinearMap = graphLineFour B at heq
  rw [← Submodule.map_comp, hmaps] at heq
  exact ⟨p, B, heq⟩

end DimensionFourDependence
