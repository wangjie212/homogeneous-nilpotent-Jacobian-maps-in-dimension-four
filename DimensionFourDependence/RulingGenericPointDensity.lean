import DimensionFourDependence.GraphLineGenericPointDensity
import DimensionFourDependence.MatrixKernelScalarExtension

/-! # Polynomial density in a two-dimensional matrix kernel

Choose an actual graph chart of the original kernel. Its linear point
equations factor through the original matrix and so still hold after
coefficient extension. A point with relative transcendence degree two
is generic in this graph chart, giving polynomial density in the kernel.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

universe u

variable {K E : Type u} [Field K] [Field E] [Algebra K E] {m : ℕ}

omit [Algebra K E] in
/-- Independence of two covectors persists through every field
embedding, as witnessed by an actual nonzero coordinate minor. -/
theorem independent_covector_pair_after_field_map {n : ℕ}
    (f : K →+* E) (v w : Fin n → K) (h : LinearIndependent K ![v, w]) :
    LinearIndependent E ![(fun i => f (v i)), (fun i => f (w i))] := by
  obtain ⟨i, j, hij⟩ := independent_pair_exists_nonzero_coordinate_minor v w h
  have he : f (v i) * f (w j) - f (v j) * f (w i) ≠ 0 := by
    intro hz
    apply hij
    apply f.injective
    simpa only [map_sub, map_mul, map_zero] using hz
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hi : a * f (v i) + b * f (w i) = 0 := by simpa using congrFun hab i
  have hj : a * f (v j) + b * f (w j) = 0 := by simpa using congrFun hab j
  have ha : a * (f (v i) * f (w j) - f (v j) * f (w i)) = 0 := by
    linear_combination f (w j) * hi - f (w i) * hj
  have hb : b * (f (v i) * f (w j) - f (v j) * f (w i)) = 0 := by
    linear_combination f (v i) * hj - f (v j) * hi
  exact ⟨(mul_eq_zero.mp ha).resolve_right he, (mul_eq_zero.mp hb).resolve_right he⟩

/-- A point in an extended two-dimensional matrix kernel with full
relative transcendence degree is polynomially dense in the original
kernel. All linear-chart and kernel-extension data are constructed. -/
theorem two_dimensional_matrix_kernel_generic_point_density
    (A : Matrix (Fin m) (Fin 4) K) (hA : finrank K (LinearMap.ker A.toLin') = 2)
    (Q : Fin 4 → E) (hQ : A.map (algebraMap K E) *ᵥ Q = 0)
    (hdim : Algebra.trdeg K (fullOutputField (K := K) Q) = 2) :
    ∀ P : MvPolynomial (Fin 4) K, aeval Q P = 0 →
      ∀ x ∈ LinearMap.ker A.toLin', aeval x P = 0 := by
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
  have hCE : C.map (algebraMap K E) *ᵥ Q = 0 :=
    matrix_kernel_le_after_scalar_extension A C hker hQ
  have hQline : Q ∈ lineChartMemberLine p (B.map (algebraMap K E)) := by
    rw [show C.map (algebraMap K E) = linePairIncidenceMatrix p p
      (B.map (algebraMap K E)) (B.map (algebraMap K E)) from
        linePairIncidenceMatrix_map (algebraMap K E) p p B B] at hCE
    exact ((linePairIncidenceMatrix_mulVec_zero_iff _ _ _ _ Q).mp hCE).1
  intro P hP x hx
  apply graph_line_generic_point_polynomial_density p B Q hQline hdim P hP x
  exact ((linePairIncidenceMatrix_mulVec_zero_iff p p B B x).mp (hker hx)).1

end DimensionFourDependence
