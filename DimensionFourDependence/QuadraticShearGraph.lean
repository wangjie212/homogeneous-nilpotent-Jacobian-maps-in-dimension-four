import DimensionFourDependence.BinaryQuadraticShear

/-! # Recovering a quadratic graph from two actual plane relation ideals

An entire principal relation ideal and a bounded-degree relation after
adding T squared force the original generator to retain degree at most
two under the inverse shear. Its graph equation then constructs the
other coordinate as a quadratic polynomial in the transcendental one.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

/-- A nonzero quadratic graph equation with a transcendental T
coordinate solves Y as an actual quadratic polynomial over the original field. -/
theorem quadratic_shear_graph_equation_solve
    (t y : F) (ht : Transcendental L t)
    (P : MvPolynomial (Option Unit) L) (hP0 : P ≠ 0) (hP : P.totalDegree ≤ 2)
    (hshift : (binaryQuadraticShear (-1) P).totalDegree ≤ 2)
    (hvalue : aeval (fun j : Option Unit => j.elim y (fun _ => t)) P = 0) :
    ∃ a b c : L, y = algebraMap L F a + algebraMap L F b * t + algebraMap L F c * t ^ 2 := by
  obtain ⟨a, b, c, f, hexp⟩ := binary_quadratic_shear_forces_graph_equation P hP hshift
  have hrel : algebraMap L F a + algebraMap L F b * y + algebraMap L F c * t +
      algebraMap L F f * t ^ 2 = 0 := by
    rw [hexp] at hvalue
    simpa only [map_add, map_mul, map_pow, aeval_C, aeval_X, Option.elim_none, Option.elim_some] using hvalue
  have hb : b ≠ 0 := by
    intro hb0
    have he : algebraMap L F a + algebraMap L F c * t + algebraMap L F f * t ^ 2 = 0 := by
      simpa only [hb0, map_zero, zero_mul, add_zero] using hrel
    have hpoly : Polynomial.C a + Polynomial.C c * Polynomial.X +
        Polynomial.C f * Polynomial.X ^ 2 = (0 : Polynomial L) := by
      apply transcendental_iff_injective.mp ht
      simpa using he
    have ha : a = 0 := by simpa using congrArg (fun Q : Polynomial L => Q.coeff 0) hpoly
    have hc : c = 0 := by simpa using congrArg (fun Q : Polynomial L => Q.coeff 1) hpoly
    have hf : f = 0 := by simpa using congrArg (fun Q : Polynomial L => Q.coeff 2) hpoly
    apply hP0
    rw [hexp, ha, hb0, hc, hf]
    simp
  refine ⟨-a / b, -c / b, -f / b, ?_⟩
  have hbF : algebraMap L F b ≠ 0 := (map_ne_zero (algebraMap L F)).mpr hb
  rw [map_div₀, map_div₀, map_div₀, map_neg, map_neg, map_neg]
  field_simp
  linear_combination hrel

/-- A nonzero relation of degree at most two after the actual square
shift, together with the entire original principal relation ideal,
constructs the quadratic graph expression for the original coordinate. -/
theorem two_quadratic_shear_relations_construct_graph
    (t y : F) (ht : Transcendental L t)
    (P Q : MvPolynomial (Option Unit) L) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (hP : P.totalDegree ≤ 2) (hQ : Q.totalDegree ≤ 2)
    (hker : RingHom.ker (aeval (fun j : Option Unit => j.elim y (fun _ => t)) :
      MvPolynomial (Option Unit) L →ₐ[L] F) = Ideal.span {P})
    (hQvalue : aeval (fun j : Option Unit => j.elim (y + t ^ 2) (fun _ => t)) Q = 0) :
    ∃ a b c : L, y = algebraMap L F a + algebraMap L F b * t + algebraMap L F c * t ^ 2 := by
  have hmem : binaryQuadraticShear 1 Q ∈ RingHom.ker
      (aeval (fun j : Option Unit => j.elim y (fun _ => t)) : MvPolynomial (Option Unit) L →ₐ[L] F) := by
    change aeval (fun j : Option Unit => j.elim y (fun _ => t)) (binaryQuadraticShear 1 Q) = 0
    rw [binaryQuadraticShear_aeval]
    simpa only [map_one, one_mul] using hQvalue
  rw [hker] at hmem
  have hdiv := map_dvd (binaryQuadraticShear (-1)).toRingHom (Ideal.mem_span_singleton.mp hmem)
  have hdiv' : binaryQuadraticShear (-1) P ∣ Q := by
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, binaryQuadraticShear_inverse] using hdiv
  have hshift : (binaryQuadraticShear (-1) P).totalDegree ≤ 2 :=
    (totalDegree_le_of_dvd_of_isDomain hdiv' hQ0).trans hQ
  have hPvalue : aeval (fun j : Option Unit => j.elim y (fun _ => t)) P = 0 := by
    change P ∈ RingHom.ker (aeval (fun j : Option Unit => j.elim y (fun _ => t)) :
      MvPolynomial (Option Unit) L →ₐ[L] F)
    rw [hker]
    exact Ideal.subset_span (by simp)
  exact quadratic_shear_graph_equation_solve t y ht P hP0 hP hshift hPvalue

end DimensionFourDependence
