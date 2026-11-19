import DimensionFourDependence.NormalizedPlaneCoordinates

/-! # Genuine and distinct graph lines from normalized directions -/

namespace DimensionFourDependence

variable {F : Type*} [Field F]

/-- The graph point and the normalized tangent vector are independent,
so their projective span is a genuine line. -/
theorem normalized_graph_line_vectors_independent
    (Y Z : Fin 3 → F) (h k : F) (a b : Fin 3)
    (hYa : Y a ≠ 0) (hZa : Z a = 0) (hZb : Z b = 1) :
    LinearIndependent F ![(Fin.snoc Y h : Fin 4 → F), (Fin.snoc Z k : Fin 4 → F)] := by
  apply normalized_radial_direction_independent (Fin.snoc Y h) (Fin.snoc Z k) a.castSucc b.castSucc
  · simpa only [Fin.snoc_castSucc] using hYa
  · simpa only [Fin.snoc_castSucc] using hZa
  · simpa only [Fin.snoc_castSucc] using hZb

/-- Two distinct directions with the same normalization give distinct
two-dimensional projective-line spans through the graph point. -/
theorem normalized_graph_line_spans_distinct
    (Y Z W : Fin 3 → F) (h k l : F) (a b : Fin 3) (hYa : Y a ≠ 0)
    (hZa : Z a = 0) (hWa : W a = 0) (hZb : Z b = 1) (hWb : W b = 1) (hZW : Z ≠ W) :
    Submodule.span F (Set.range ![(Fin.snoc Y h : Fin 4 → F), (Fin.snoc Z k : Fin 4 → F)]) ≠
      Submodule.span F (Set.range ![(Fin.snoc Y h : Fin 4 → F), (Fin.snoc W l : Fin 4 → F)]) := by
  intro heq
  let A : Fin 4 → F := Fin.snoc Y h
  let V : Fin 4 → F := Fin.snoc Z k
  let U : Fin 4 → F := Fin.snoc W l
  have hU : U ∈ Submodule.span F (Set.range ![A, V]) := by
    change U ∈ Submodule.span F (Set.range ![(Fin.snoc Y h : Fin 4 → F), (Fin.snoc Z k : Fin 4 → F)])
    rw [heq]
    exact Submodule.subset_span ⟨1, rfl⟩
  have hV : V ∈ Submodule.span F (Set.range ![A, V]) := Submodule.subset_span ⟨1, rfl⟩
  have hz : U - V = 0 := by
    apply normalized_radial_plane_vector_zero A V (U - V) a.castSucc b.castSucc
    · simpa only [A, Fin.snoc_castSucc] using hYa
    · simpa only [V, Fin.snoc_castSucc] using hZa
    · simpa only [V, Fin.snoc_castSucc] using hZb
    · exact Submodule.sub_mem _ hU hV
    · simp only [Pi.sub_apply, U, V, Fin.snoc_castSucc, hWa, hZa, sub_self]
    · simp only [Pi.sub_apply, U, V, Fin.snoc_castSucc, hWb, hZb, sub_self]
  apply hZW
  funext i
  have hi := congrFun (sub_eq_zero.mp hz) i.castSucc
  simpa only [U, V, Fin.snoc_castSucc] using hi.symm

end DimensionFourDependence
