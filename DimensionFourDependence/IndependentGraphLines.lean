import DimensionFourDependence.NormalizedGraphLines

/-! # Distinct graph lines from directions independent modulo the radial point

Independence of the three-coordinate radial point and directions
survives graph lifting. Thus the two lines through the graph point are
distinct even when the normalized unit coordinates differ.
-/

namespace DimensionFourDependence

variable {F : Type*} [Field F]

/-- Independent radial and direction vectors stay independent after
adding their fourth graph coordinates. -/
theorem graph_lifts_triple_independent
    (Y Z W : Fin 3 → F) (hli : LinearIndependent F ![Y, Z, W]) (h k l : F) :
    LinearIndependent F ![(Fin.snoc Y h : Fin 4 → F), (Fin.snoc Z k : Fin 4 → F),
      (Fin.snoc W l : Fin 4 → F)] := by
  let π : (Fin 4 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := fun v i => v i.castSucc
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp π
  have he : π ∘ ![(Fin.snoc Y h : Fin 4 → F), (Fin.snoc Z k : Fin 4 → F),
      (Fin.snoc W l : Fin 4 → F)] = ![Y, Z, W] := by
    funext i j
    fin_cases i <;> simp [π, Fin.snoc_castSucc]
  rw [he]
  exact hli

/-- A linearly independent point and two direction vectors give
distinct line spans through that point. -/
theorem line_spans_distinct_of_independent_triple {n : ℕ}
    (A V U : Fin n → F) (hli : LinearIndependent F ![A, V, U]) :
    Submodule.span F (Set.range ![A, V]) ≠ Submodule.span F (Set.range ![A, U]) := by
  intro heq
  have hU : U ∈ Submodule.span F (Set.range ![A, V]) := by
    rw [heq]
    exact Submodule.subset_span ⟨1, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := F)).mp hU
  have he : c 0 • A + c 1 • V = U := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hc
  have hrel : c 0 • A + c 1 • V + (-1 : F) • U = 0 := by
    rw [he]
    simp only [neg_one_smul, add_neg_cancel]
  have hz := Fintype.linearIndependent_iff.mp hli ![c 0, c 1, -1]
    (by simpa [Fin.sum_univ_succ, add_assoc] using hrel)
  exact (neg_ne_zero.mpr one_ne_zero) (hz 2)

/-- Simultaneously permuting all vector coordinates preserves independence. -/
theorem independent_triple_precompose_equiv {n : ℕ}
    (A V U : Fin n → F) (hli : LinearIndependent F ![A, V, U]) (p : Equiv.Perm (Fin n)) :
    LinearIndependent F ![A ∘ p, V ∘ p, U ∘ p] := by
  let π : (Fin n → F) →ₗ[F] (Fin n → F) :=
    { toFun := fun v j => v (p.symm j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp π
  have he : π ∘ ![A ∘ p, V ∘ p, U ∘ p] = ![A, V, U] := by
    funext i j
    fin_cases i <;> simp [π, Function.comp_def]
  rw [he]
  exact hli

/-- Independent directions modulo the radial vector give distinct
graph-line spans without requiring a common unit-coordinate normalization. -/
theorem graph_lifts_line_spans_distinct
    (Y Z W : Fin 3 → F) (hli : LinearIndependent F ![Y, Z, W]) (h k l : F) :
    Submodule.span F (Set.range ![(Fin.snoc Y h : Fin 4 → F), (Fin.snoc Z k : Fin 4 → F)]) ≠
      Submodule.span F (Set.range ![(Fin.snoc Y h : Fin 4 → F), (Fin.snoc W l : Fin 4 → F)]) := by
  exact line_spans_distinct_of_independent_triple _ _ _ (graph_lifts_triple_independent Y Z W hli h k l)

end DimensionFourDependence
