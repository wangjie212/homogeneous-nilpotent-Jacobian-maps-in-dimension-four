import DimensionFourDependence.LinearlyDisjointProjectiveHilbert
import DimensionFourDependence.GenericDirectionTangent

/-! # Positive source-curve degree descends through independent algebraic coefficient residues -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K C F σ : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Field C] [Field F] [Algebra K C] [Algebra C F] [Algebra K F]
  [IsScalarTower K C F] [Finite σ]

/-- A fixed original curve with a source coordinate transcendental
over the extended coefficients has exactly the same homogeneous
Hilbert function over those coefficients and over the original constants. -/
theorem fixed_curve_projective_hilbert_eq_independent_coefficients
    (z : σ → F)
    (hcurve : Algebra.trdeg K (IntermediateField.adjoin K (Set.range z)) ≤ 1)
    (htrans : ∃ i, Transcendental C (z i)) (n : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := C) z).toIdeal n =
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := K) z).toIdeal n := by
  let J := IntermediateField.adjoin K (Set.range z)
  let x : σ → J := fun i => ⟨z i, IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩
  obtain ⟨i, hi⟩ := htrans
  have hx : (fun j => algebraMap J F (x j)) = z := by funext j; rfl
  have ht : Transcendental C (algebraMap J F (x i)) := hi
  have hdisj := curve_coefficient_linearDisjoint_of_transcendental_parameter J hcurve (x i) ht
  have he := projectiveHilbertFunction_point_eq_of_linearlyDisjoint J hdisj x n
  have hf := projectiveFieldPointIdeal_algHom x (IsScalarTower.toAlgHom K J F)
  change (projectiveFieldPointIdeal (E := K) (fun j => algebraMap J F (x j))).toIdeal =
    (projectiveFieldPointIdeal (E := K) x).toIdeal at hf
  rw [hx] at he hf
  rw [hf]
  exact he

variable {E : Type*} [Field E] [Algebra E C] [Algebra E F]
  [IsScalarTower E C F] [Algebra.IsAlgebraic E C]

/-- Algebraic extension of the parameter constants preserves the
same original-coordinate Hilbert function when a genuine curve coordinate
was already transcendental over the parameter constants. -/
theorem fixed_curve_projective_hilbert_eq_algebraic_coefficients
    (z : σ → F)
    (hcurve : Algebra.trdeg K (IntermediateField.adjoin K (Set.range z)) ≤ 1)
    (htrans : ∃ i, Transcendental E (z i)) (n : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := C) z).toIdeal n =
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := K) z).toIdeal n := by
  obtain ⟨i, hi⟩ := htrans
  apply fixed_curve_projective_hilbert_eq_independent_coefficients z hcurve _ n
  exact ⟨i, fun h => hi (h.restrictScalars E)⟩

/-- The actual positive degree, rather than only an inequality,
is unchanged under the same independent algebraic coefficient extension. -/
theorem fixed_curve_projective_degree_iff_algebraic_coefficients
    (z : σ → F)
    (hcurve : Algebra.trdeg K (IntermediateField.adjoin K (Set.range z)) ≤ 1)
    (htrans : ∃ i, Transcendental E (z i)) (D : ℕ) :
    HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C) z).toIdeal D ↔
      HasCurveHilbertDegree (projectiveFieldPointIdeal (E := K) z).toIdeal D := by
  simp only [HasCurveHilbertDegree,
    fixed_curve_projective_hilbert_eq_algebraic_coefficients z hcurve htrans]

/-- A constructed positive specialized degree at most two now
bounds the fixed original source curve over its original algebraically
closed constants. No original curve degree is assumed. -/
theorem fixed_curve_positive_degree_at_most_two_descends
    (z : σ → F)
    (hcurve : Algebra.trdeg K (IntermediateField.adjoin K (Set.range z)) ≤ 1)
    (htrans : ∃ i, Transcendental E (z i))
    (hdegree : ∃ D : ℕ, D ≤ 2 ∧ HasCurveHilbertDegree
      (projectiveFieldPointIdeal (E := C) z).toIdeal D) :
    ∃ D : ℕ, D ≤ 2 ∧ HasCurveHilbertDegree (projectiveFieldPointIdeal (E := K) z).toIdeal D := by
  obtain ⟨D, hD2, hD⟩ := hdegree
  exact ⟨D, hD2, (fixed_curve_projective_degree_iff_algebraic_coefficients z hcurve htrans D).mp hD⟩

end DimensionFourDependence
