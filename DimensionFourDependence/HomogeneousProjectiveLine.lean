import DimensionFourDependence.HomogeneousEvaluationScaling

/-! # From an affine line identity to its full projective span

A homogeneous equation vanishing identically on `O + t D` vanishes on
the entire vector span of `O,D`, including the direction at infinity.
The direction point is obtained by polynomial identity over an infinite
extension field, without an assumed projective-closure assertion.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {n : ℕ}

/-- Scalar evaluation of the polynomial restriction to an affine line. -/
theorem polynomial_affine_line_aeval (R : MvPolynomial (Fin n) K)
    (O D : Fin n → E) (t : E) :
    Polynomial.aeval t (aeval (fun i => Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X) R) =
      aeval (fun i => O i + t * D i) R := by
  have he := comp_aeval_apply (fun i => Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X)
    ((Polynomial.aeval t).restrictScalars K) R
  have hpoint : (fun i => ((Polynomial.aeval t).restrictScalars K)
      (Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X)) = (fun i => O i + t * D i) := by
    funext i
    change Polynomial.aeval t (Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X) = _
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self_apply]
    ring
  rw [hpoint] at he
  exact he

/-- Homogeneity extends an affine line identity to every span point
whose coefficient of the base point is nonzero. -/
theorem homogeneous_line_nonzero_base_coefficient
    (R : MvPolynomial (Fin n) K) {d : ℕ} (hR : R.IsHomogeneous d)
    (O D : Fin n → E)
    (hline : aeval (fun i => Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X) R = 0)
    (a b : E) (ha : a ≠ 0) : aeval (fun i => a * O i + b * D i) R = 0 := by
  have ht : aeval (fun i => O i + (b / a) * D i) R = 0 := by
    have he := congrArg (Polynomial.aeval (b / a)) hline
    rw [polynomial_affine_line_aeval, map_zero] at he
    exact he
  have hpoint : (fun i => a * O i + b * D i) = (fun i => a * (O i + (b / a) * D i)) := by
    funext i
    field_simp
  rw [hpoint, homogeneous_aeval_scale R hR, ht, mul_zero]

/-- The direction at infinity also satisfies the original homogeneous equation. -/
theorem homogeneous_affine_line_direction [Infinite E]
    (R : MvPolynomial (Fin n) K) {d : ℕ} (hR : R.IsHomogeneous d)
    (O D : Fin n → E)
    (hline : aeval (fun i => Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X) R = 0) :
    aeval D R = 0 := by
  let P : Polynomial E := aeval (fun i => Polynomial.C (D i) + Polynomial.C (O i) * Polynomial.X) R
  have hroot (a : E) (ha : a ≠ 0) : Polynomial.IsRoot P a := by
    change Polynomial.aeval a P = 0
    change Polynomial.aeval a (aeval (fun i => Polynomial.C (D i) + Polynomial.C (O i) * Polynomial.X) R) = 0
    rw [polynomial_affine_line_aeval]
    have he : (fun i => D i + a * O i) = (fun i => a * O i + 1 * D i) := by
      funext i
      ring
    rw [he]
    exact homogeneous_line_nonzero_base_coefficient R hR O D hline a 1 ha
  have hinf : Set.Infinite {a : E | a ≠ 0} := by
    convert Set.infinite_univ.sdiff (Set.finite_singleton (0 : E)) using 1
    ext a
    simp
  have hP : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P (hinf.mono (fun a ha => hroot a ha))
  have he : Polynomial.aeval 0 P = aeval D R := by
    change Polynomial.aeval 0 (aeval (fun i => Polynomial.C (D i) + Polynomial.C (O i) * Polynomial.X) R) = _
    rw [polynomial_affine_line_aeval]
    simp only [zero_mul, add_zero]
  rw [hP, map_zero] at he
  exact he.symm

/-- An affine line identity in a homogeneous equation gives full projective-line containment. -/
theorem homogeneous_affine_line_span_contained [Infinite E]
    (R : MvPolynomial (Fin n) K) {d : ℕ} (hR : R.IsHomogeneous d)
    (O D : Fin n → E)
    (hline : aeval (fun i => Polynomial.C (O i) + Polynomial.C (D i) * Polynomial.X) R = 0) :
    ∀ x ∈ Submodule.span E (Set.range ![O, D]), aeval x R = 0 := by
  intro x hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := E)).mp hx
  have he : c 0 • O + c 1 • D = x := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hc
  rw [← he]
  change aeval (fun i => c 0 * O i + c 1 * D i) R = 0
  by_cases hzero : c 0 = 0
  · simp only [hzero, zero_mul, zero_add]
    rw [homogeneous_aeval_scale R hR, homogeneous_affine_line_direction R hR O D hline, mul_zero]
  · exact homogeneous_line_nonzero_base_coefficient R hR O D hline (c 0) (c 1) hzero

end DimensionFourDependence
