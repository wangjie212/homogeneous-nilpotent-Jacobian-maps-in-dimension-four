import DimensionFourDependence.ParabolaCoordinateUnits
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # A polynomial nowhere zero on the actual affine parabola is constant

Over algebraically closed coefficients, a nonunit polynomial in the
constructed actual coordinate algebra has a root. Evaluation at that
root is an actual coefficient-algebra point of the original coordinate
quotient. Thus a function nonzero at every actual point is a unit and
therefore a nonzero original-field constant. The usual original-equation
zero-locus formulation is also derived.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L : Type*} [Field L] [IsAlgClosed L]

/-- In a polynomial algebra over algebraically closed coefficients,
a function nonzero at every actual coefficient-algebra point is invertible. -/
theorem polynomial_algebra_equiv_nowhere_zero_is_unit
    {A : Type*} [CommRing A] [Algebra L A]
    (e : Polynomial L ≃ₐ[L] A) (v : A)
    (hnonzero : ∀ phi : A →ₐ[L] L, phi v ≠ 0) : IsUnit v := by
  let P := e.symm v
  by_cases hdegree : P.degree = 0
  · have hu := (Polynomial.isUnit_iff_degree_eq_zero.mpr hdegree).map e.toMonoidHom
    change IsUnit (e (e.symm v)) at hu
    simpa only [AlgEquiv.apply_symm_apply] using hu
  · obtain ⟨r, hr⟩ := IsAlgClosed.exists_root P hdegree
    exfalso
    apply (hnonzero ((Polynomial.aeval r).comp e.symm.toAlgHom))
    simpa [Polynomial.aeval_def, Polynomial.IsRoot, P] using hr

variable {F : Type*} [Field F] [Algebra L F]

/-- A polynomial nonzero at every actual point of the original
parabola coordinate quotient has a nonzero original-field value. -/
theorem parabola_polynomial_nonvanishing_at_quotient_points_constant
    (x : Fin 4 → F) (hx : LiesInAffineParabola (L := L) x)
    (P : MvPolynomial (Fin 4) L)
    (hnonzero : ∀ phi : (MvPolynomial (Fin 4) L ⧸ fiberVanishingIdeal (L := L) x) →ₐ[L] L,
      phi (Ideal.Quotient.mk (fiberVanishingIdeal (L := L) x) P) ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ aeval x P = algebraMap L F c := by
  obtain ⟨e⟩ := parabola_coordinate_quotient_polynomial_equiv x hx
  exact parabola_polynomial_unit_mod_relations_constant x hx P
    (polynomial_algebra_equiv_nowhere_zero_is_unit e _ hnonzero)

/-- The same assertion for the ordinary original-coordinate zero
locus of the entire actual affine relation ideal. -/
theorem parabola_polynomial_nonvanishing_on_original_zero_locus_constant
    (x : Fin 4 → F) (hx : LiesInAffineParabola (L := L) x)
    (P : MvPolynomial (Fin 4) L)
    (hnonzero : ∀ z : Fin 4 → L,
      (∀ Q ∈ fiberVanishingIdeal (L := L) x, aeval z Q = 0) → aeval z P ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ aeval x P = algebraMap L F c := by
  apply parabola_polynomial_nonvanishing_at_quotient_points_constant x hx P
  intro phi
  let z : Fin 4 → L := fun i => phi (Ideal.Quotient.mk (fiberVanishingIdeal (L := L) x) (X i))
  have heval (Q : MvPolynomial (Fin 4) L) :
      aeval z Q = phi (Ideal.Quotient.mk (fiberVanishingIdeal (L := L) x) Q) := by
    have he : aeval z = phi.comp (Ideal.Quotient.mkₐ L (fiberVanishingIdeal (L := L) x)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [aeval_X, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, z]
    exact DFunLike.congr_fun he Q
  have hz : ∀ Q ∈ fiberVanishingIdeal (L := L) x, aeval z Q = 0 := by
    intro Q hQ
    rw [heval Q, Ideal.Quotient.eq_zero_iff_mem.mpr hQ, map_zero]
  have hn := hnonzero z hz
  rwa [heval P] at hn

end DimensionFourDependence
