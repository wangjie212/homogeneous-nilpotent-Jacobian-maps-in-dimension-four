import DimensionFourDependence.HomogenizedDivisorLift

/-! # Primitive homogeneous vectors remain primitive on source charts

A common chart divisor homogenizes to a common divisor in the original
coordinates. Primitivity makes that homogeneous divisor a unit, and its
dehomogenization is the original chart divisor. Consequently chart
prime-power orders lie entirely in the original homogeneous common factor.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K σ τ : Type*} [Field K] {n : ℕ}

/-- Polynomial coordinate isomorphisms preserve vector primitivity. -/
theorem isPrimitiveVec_map_algEquiv
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K)
    (P : Fin n → MvPolynomial σ K) (hP : IsPrimitiveVec P) :
    IsPrimitiveVec (fun i => e (P i)) := by
  intro p hp
  have hu : IsUnit (e.symm p) := hP (e.symm p) (fun i => by
    simpa using map_dvd e.symm.toRingHom (hp i))
  simpa using hu.map e.toRingHom

/-- A primitive vector whose components have a common homogeneous
degree remains primitive on every standard affine projective chart. -/
theorem isPrimitiveVec_projectiveDehomogenize
    (P : Fin n → MvPolynomial (Option σ) K) {d : ℕ}
    (hP : IsHomogMap P d) (hprim : IsPrimitiveVec P) :
    IsPrimitiveVec (fun i => projectiveDehomogenize (P i)) := by
  intro p hp
  have hu : IsUnit (projectiveHomogenize p p.totalDegree) :=
    hprim _ (fun i => homogenized_chart_divisor_dvd_homogeneous (P i) (hP i) p (hp i))
  have hm := hu.map (projectiveDehomogenize (R := K) (σ := σ)).toRingHom
  change IsUnit (projectiveDehomogenize (projectiveHomogenize p p.totalDegree)) at hm
  simpa only [projectiveDehomogenize_homogenize] using hm

/-- Chart prime-power divisibility of every homogeneous map component
forces divisibility of its original homogeneous common factor and the
precise original degree bound, without replacing it by a chart gcd. -/
theorem dehomogenized_source_common_factor_degree
    (H P : Fin n → MvPolynomial (Option σ) K)
    (g : MvPolynomial (Option σ) K) {c d : ℕ}
    (hg : g ≠ 0) (hgh : g.IsHomogeneous c) (hP : IsHomogMap P d)
    (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (δ : MvPolynomial σ K) (hδ : Irreducible δ) (a : ℕ)
    (hdiv : ∀ i, δ ^ a ∣ projectiveDehomogenize (H i)) :
    projectiveHomogenize δ δ.totalDegree ^ a ∣ g ∧
      a * δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  have hdg : projectiveDehomogenize g ≠ 0 := by
    intro hz
    exact hg (homogeneous_dehomogenize_eq_zero g hgh hz)
  have hprim' := isPrimitiveVec_projectiveDehomogenize P hP hprim
  have hHP' : (fun i => projectiveDehomogenize (H i)) =
      (fun i => projectiveDehomogenize g * projectiveDehomogenize (P i)) := by
    funext i
    rw [congrFun hHP i, map_mul]
  obtain ⟨hδg, hdeg, hsmall⟩ := source_divisor_multiplicity_common_factor_degree
    (fun i => projectiveDehomogenize (H i)) (fun i => projectiveDehomogenize (P i))
    (projectiveDehomogenize g) hdg hprim' hHP' δ hδ a hdiv
  have hlift := homogenized_chart_divisor_dvd_homogeneous g hgh (δ ^ a) hδg
  rw [totalDegree_pow_eq_of_ne_zero δ hδ.ne_zero a,
    projectiveHomogenize_pow_actual δ hδ.ne_zero a] at hlift
  exact ⟨hlift, hdeg.trans (projectiveDehomogenize_totalDegree g),
    hsmall.trans (projectiveDehomogenize_totalDegree g)⟩

end DimensionFourDependence
