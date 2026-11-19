import DimensionFourDependence.RulingGenericPointDensity

/-! # Polynomial identities on rulings survive field extension

A two-dimensional linear kernel admits a graph chart. Over an infinite
field, vanishing on all its points is identical vanishing of a binary
polynomial. That identity can then be evaluated at points over any field
extension, including the residue fields of actual boundary points.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

variable {K E : Type u} [Field K] [Field E] [Algebra K E] [Infinite K]

/-- A polynomial identity on an original graph line holds at all points
of that same graph line over an arbitrary extension field. -/
theorem graph_line_polynomial_vanishing_scalar_extension
    (p : Equiv.Perm (Fin 4)) (B : Matrix (Fin 2) (Fin 2) K)
    (P : MvPolynomial (Fin 4) K)
    (hP : ∀ x ∈ lineChartMemberLine p B, aeval x P = 0)
    (Q : Fin 4 → E) (hQ : Q ∈ lineChartMemberLine p (B.map (algebraMap K E))) :
    aeval Q P = 0 := by
  have hrestrict : graphLineRestriction B (rename p.symm P) = 0 := by
    apply MvPolynomial.funext
    intro u
    change aeval u (graphLineRestriction B (rename p.symm P)) =
      aeval u (0 : MvPolynomial (Fin 2) K)
    rw [graphLineRestriction_eval_extension, map_zero]
    exact hP _ ⟨_, (mem_graphLineFour B _).mpr ⟨u, rfl⟩, rfl⟩
  obtain ⟨z, hz, hzQ⟩ := hQ
  obtain ⟨u, hu⟩ := (mem_graphLineFour _ _).mp hz
  have hQcoord : Q = fun i => (![u 0, u 1,
      (B.map (algebraMap K E) *ᵥ u) 0, (B.map (algebraMap K E) *ᵥ u) 1]) (p.symm i) := by
    rw [← hzQ, hu]
    rfl
  rw [hQcoord, ← graphLineRestriction_eval_extension, hrestrict, map_zero]

/-- Polynomial identities on a two-dimensional matrix kernel persist
at every point of its coefficient extension. -/
theorem two_dimensional_matrix_kernel_vanishing_scalar_extension
    {m : ℕ} (A : Matrix (Fin m) (Fin 4) K)
    (hA : Module.finrank K (LinearMap.ker A.toLin') = 2)
    (P : MvPolynomial (Fin 4) K)
    (hP : ∀ x ∈ LinearMap.ker A.toLin', aeval x P = 0)
    (Q : Fin 4 → E) (hQ : A.map (algebraMap K E) *ᵥ Q = 0) :
    aeval Q P = 0 := by
  obtain ⟨p, B, hmap⟩ := projective_line_exists_graph_chart (LinearMap.ker A.toLin') hA
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
  have hQline : Q ∈ lineChartMemberLine p (B.map (algebraMap K E)) := by
    rw [show C.map (algebraMap K E) =
      linePairIncidenceMatrix p p (B.map (algebraMap K E)) (B.map (algebraMap K E)) from
      linePairIncidenceMatrix_map _ _ _ _ _] at hCE
    exact ((linePairIncidenceMatrix_mulVec_zero_iff _ _ _ _ _).mp hCE).1
  apply graph_line_polynomial_vanishing_scalar_extension p B P _ Q hQline
  intro x hx
  apply hP x
  have hh : (lineCoordinatePermutation p) x ∈
      (LinearMap.ker A.toLin').map (lineCoordinatePermutation p).toLinearMap := by
    rw [hmap]
    obtain ⟨z, hz, hzQ⟩ := hx
    have he : (lineCoordinatePermutation p) x = z := by
      rw [← hzQ]
      exact (lineCoordinatePermutation p).apply_symm_apply z
    rw [he]
    exact hz
  obtain ⟨y, hy, he⟩ := hh
  have hyx : y = x := (lineCoordinatePermutation p).injective he
  exact hyx ▸ hy

/-- A full-dimensional point on the original ruling determines every
polynomial relation at points of that ruling over any extension field. -/
theorem two_dimensional_matrix_kernel_generic_point_density_extension
    {F : Type u} [Field F] [Algebra K F]
    {m : ℕ} (A : Matrix (Fin m) (Fin 4) K)
    (hA : Module.finrank K (LinearMap.ker A.toLin') = 2)
    (Q : Fin 4 → E) (hQ : A.map (algebraMap K E) *ᵥ Q = 0)
    (hdim : Algebra.trdeg K (fullOutputField (K := K) Q) = 2)
    (P : MvPolynomial (Fin 4) K) (hP : aeval Q P = 0)
    (b : Fin 4 → F) (hb : A.map (algebraMap K F) *ᵥ b = 0) :
    aeval b P = 0 :=
  two_dimensional_matrix_kernel_vanishing_scalar_extension A hA P
    (two_dimensional_matrix_kernel_generic_point_density A hA Q hQ hdim P hP) b hb

end DimensionFourDependence
