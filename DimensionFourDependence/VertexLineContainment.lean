import DimensionFourDependence.Defs

/-! # Vertex-line equations give actual line containment

The transverse two-by-two equations with one nonzero original-field
direction coordinate put a source point in the span of that direction
and the fixed fourth axis. Polynomial ideal membership therefore gives
containment for every field-valued point of the same closed component.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The actual transverse line equations construct the two scalar
coordinates of a point in the line through the specified vertex. -/
theorem vertex_line_equations_point_mem_span
    (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0) (y : Fin 4 → F)
    (hy : ∀ i : Fin 3, algebraMap K F (b j) * y i.castSucc =
      algebraMap K F (b i) * y j.castSucc) :
    y ∈ Submodule.span F ({Fin.snoc (fun i : Fin 3 => algebraMap K F (b i)) 0,
      Fin.snoc (0 : Fin 3 → F) 1} : Set (Fin 4 → F)) := by
  let V : Fin 4 → F := Fin.snoc (fun i : Fin 3 => algebraMap K F (b i)) 0
  let a : Fin 4 → F := Fin.snoc (0 : Fin 3 → F) 1
  let c := y j.castSucc / algebraMap K F (b j)
  have hjF : algebraMap K F (b j) ≠ 0 := (_root_.map_ne_zero _).mpr hj
  have he : y = c • V + y (Fin.last 3) • a := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Pi.add_apply, Pi.smul_apply, V, a, Fin.snoc_last,
        smul_eq_mul, mul_zero, zero_add, mul_one]
    · simp only [Pi.add_apply, Pi.smul_apply, V, a, Fin.snoc_castSucc, Pi.zero_apply,
        smul_eq_mul, mul_zero, add_zero]
      apply mul_left_cancel₀ hjF
      rw [hy i]
      dsimp only [c]
      field_simp
  rw [he]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [V]))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [a]))

/-- Original line equations in a component ideal put every
field-valued point of that same component on the same vertex line. -/
theorem ideal_vertex_line_equations_all_points_mem_span
    (Q : Ideal (MvPolynomial (Fin 4) K)) (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0)
    (hline : ∀ i : Fin 3, C (b j) * X i.castSucc - C (b i) * X j.castSucc ∈ Q)
    (y : Fin 4 → F) (hy : ∀ P ∈ Q, aeval y P = 0) :
    y ∈ Submodule.span F ({Fin.snoc (fun i : Fin 3 => algebraMap K F (b i)) 0,
      Fin.snoc (0 : Fin 3 → F) 1} : Set (Fin 4 → F)) := by
  apply vertex_line_equations_point_mem_span b j hj y
  intro i
  have he := hy _ (hline i)
  simpa only [map_sub, map_mul, aeval_C, aeval_X, sub_eq_zero] using he

end DimensionFourDependence
