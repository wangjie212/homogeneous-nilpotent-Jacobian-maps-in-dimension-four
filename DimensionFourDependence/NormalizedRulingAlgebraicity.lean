import DimensionFourDependence.AlgebraicProjectiveLineRoots

/-! # A nonalgebraic normalized ruling point is projectively generic

The same graph chart contains points of a two-dimensional matrix kernel
over arbitrary extension fields. If a normalized point is not algebraic,
every homogeneous equation it satisfies vanishes on that entire line.
It therefore has the same homogeneous relations as a generic line point.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

variable {K E F : Type u} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]

/-- An actual graph chart of a matrix kernel contains every point of
that kernel after arbitrary field extension. -/
theorem matrix_kernel_mem_graph_chart_after_extension
    {m : ℕ} (A : Matrix (Fin m) (Fin 4) K) (p : Equiv.Perm (Fin 4))
    (B : Matrix (Fin 2) (Fin 2) K)
    (hmap : (LinearMap.ker A.toLin').map (lineCoordinatePermutation p).toLinearMap = graphLineFour B)
    (Q : Fin 4 → E) (hQ : A.map (algebraMap K E) *ᵥ Q = 0) :
    Q ∈ lineChartMemberLine p (B.map (algebraMap K E)) := by
  let C := linePairIncidenceMatrix p p B B
  have hker : LinearMap.ker A.toLin' ≤ LinearMap.ker C.toLin' := by
    intro x hx
    have hxline : x ∈ lineChartMemberLine p B := by
      refine ⟨(lineCoordinatePermutation p) x, ?_, ?_⟩
      · rw [← hmap]
        exact ⟨x, hx, rfl⟩
      · exact (lineCoordinatePermutation p).symm_apply_apply x
    exact (linePairIncidenceMatrix_mulVec_zero_iff p p B B x).mpr ⟨hxline, hxline⟩
  have hCE := matrix_kernel_le_after_scalar_extension A C hker hQ
  rw [show C.map (algebraMap K E) =
    linePairIncidenceMatrix p p (B.map (algebraMap K E)) (B.map (algebraMap K E)) from
    linePairIncidenceMatrix_map _ _ _ _ _] at hCE
  exact ((linePairIncidenceMatrix_mulVec_zero_iff _ _ _ _ _).mp hCE).1

variable [Infinite K]

/-- A normalized nonalgebraic point on a two-dimensional kernel has
no homogeneous relation beyond those of the entire original line. -/
theorem normalized_kernel_non_algebraic_homogeneous_relation
    {m : ℕ} (A : Matrix (Fin m) (Fin 4) K)
    (hA : Module.finrank K (LinearMap.ker A.toLin') = 2)
    (Q : Fin 4 → E) (hQ : A.map (algebraMap K E) *ᵥ Q = 0)
    (b : Fin 4 → F) (hb : A.map (algebraMap K F) *ᵥ b = 0)
    (a : Fin 4) (ha : b a = 1) (halg : ¬ ∀ i, IsAlgebraic K (b i))
    (P : MvPolynomial (Fin 4) K) {d : ℕ} (hP : P.IsHomogeneous d) (hzero : aeval b P = 0) :
    aeval Q P = 0 := by
  obtain ⟨p, B, hmap⟩ := projective_line_exists_graph_chart (LinearMap.ker A.toLin') hA
  have hbline := matrix_kernel_mem_graph_chart_after_extension A p B hmap b hb
  have hQline := matrix_kernel_mem_graph_chart_after_extension A p B hmap Q hQ
  have hrestrict : graphLineRestriction B (rename p.symm P) = 0 := by
    by_contra hn
    exact halg (normalized_graph_line_root_coordinates_isAlgebraic p B P hP hn b hbline hzero a ha)
  apply graph_line_polynomial_vanishing_scalar_extension p B P _ Q hQline
  exact hypersurfaceAtlasLine_contained P ⟨p, ⟨B, hrestrict⟩⟩

/-- A normalized nonalgebraic point on a two-dimensional kernel has
exactly the homogeneous relations of any full-dimensional generic point
of that kernel. Both directions are derived from actual line equations. -/
theorem normalized_kernel_non_algebraic_generic_homogeneous_relations
    {m : ℕ} (A : Matrix (Fin m) (Fin 4) K)
    (hA : Module.finrank K (LinearMap.ker A.toLin') = 2)
    (Q : Fin 4 → E) (hQ : A.map (algebraMap K E) *ᵥ Q = 0)
    (hdim : Algebra.trdeg K (fullOutputField (K := K) Q) = 2)
    (b : Fin 4 → F) (hb : A.map (algebraMap K F) *ᵥ b = 0)
    (a : Fin 4) (ha : b a = 1) (halg : ¬ ∀ i, IsAlgebraic K (b i))
    (P : MvPolynomial (Fin 4) K) {d : ℕ} (hP : P.IsHomogeneous d) :
    aeval b P = 0 ↔ aeval Q P = 0 := by
  constructor
  · exact normalized_kernel_non_algebraic_homogeneous_relation A hA Q hQ b hb a ha halg P hP
  · intro hzero
    exact two_dimensional_matrix_kernel_generic_point_density_extension A hA Q hQ hdim P hzero b hb

end DimensionFourDependence
