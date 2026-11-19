import DimensionFourDependence.ProjectiveOriginLocalHilbertBound
import DimensionFourDependence.HyperplaneSectionHilbertDegree

/-! # A single-support hyperplane section bounds the actual curve degree

The actual hyperplane-section recurrence supplies its eventual Hilbert
value from the curve degree. The proved injection into the actual local
chart ring bounds that value by its local coefficient dimension. The
coordinate hyperplane and standard affine chart may be different.
-/

namespace DimensionFourDependence

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F sigma : Type*} [Field F] [Finite sigma]

/-- A homogeneous prime curve's actual Hilbert degree is bounded by
the actual local dimension of a hyperplane section supported at the
standard rational chart origin. The section Hilbert value and its
comparison to the local algebra are both derived internally. -/
theorem curve_hilbert_degree_le_of_single_origin_hyperplane_section
    (I : Ideal (MvPolynomial (Option sigma) F)) [I.IsPrime]
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option sigma) F))
    (i : Option sigma) (hi : X i ∉ I) {e m : ℕ} (he : HasCurveHilbertDegree I e)
    (hsupport : ∀ z : ProjectiveSpectrum (homogeneousSubmodule (Option sigma) F),
      I ⊔ Ideal.span ({X i} : Set (MvPolynomial (Option sigma) F)) ≤ z.asHomogeneousIdeal.toIdeal →
        z = projectiveChartOriginPoint)
    (hlocal : ∃ hJ : projectiveDehomogenizedIdeal
        (I ⊔ Ideal.span ({X i} : Set (MvPolynomial (Option sigma) F))) ≤
          RingHom.ker (aeval (fun _ : sigma => (0 : F))).toRingHom,
      let R := Localization.AtPrime (zeroPointQuotientPrime (projectiveDehomogenizedIdeal
        (I ⊔ Ideal.span ({X i} : Set (MvPolynomial (Option sigma) F)))) hJ)
      Module.Finite F R ∧ finrank F R ≤ m) : e ≤ m := by
  obtain ⟨hJ, hfin, hbound⟩ := hlocal
  let := hfin
  obtain ⟨N, hN⟩ := hyperplane_section_eventual_hilbert_dimension I hI i hi he
  have hvalue : ∀ n ≥ N + 1,
      projectiveHilbertFunction (I ⊔ Ideal.span ({X i} : Set (MvPolynomial (Option sigma) F))) n = e := by
    intro n hn
    have heq : n - 1 + 1 = n := by omega
    simpa only [heq] using hN (n - 1) (by omega)
  exact (projective_hilbert_value_le_actual_origin_local_dimension
    (I ⊔ Ideal.span ({X i} : Set (MvPolynomial (Option sigma) F)))
    (sup_coordinate_isHomogeneous I hI i) hJ e (N + 1) hvalue hsupport).trans hbound

end DimensionFourDependence
