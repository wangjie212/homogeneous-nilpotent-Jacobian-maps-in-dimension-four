import DimensionFourDependence.ParabolaCoordinateAlgebra
import Mathlib.Algebra.Polynomial.Degree.Units

/-! # Invertible actual parabola functions are original-field constants

Transport polynomial units through the constructed coordinate algebra
isomorphism. This proves the constant-function assertion for units of
the entire actual affine quotient, without choosing a presentation of
an invertible regular function or assuming a geometric classification.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L : Type*} [Field L]

/-- Every unit of an algebra identified with a polynomial ring is
a unit of the original coefficient field. -/
theorem polynomial_algebra_equiv_unit_is_coefficient
    {A : Type*} [CommRing A] [Algebra L A]
    (e : Polynomial L ≃ₐ[L] A) (v : A) (hv : IsUnit v) :
    ∃ c : L, IsUnit c ∧ algebraMap L A c = v := by
  have hP : IsUnit (e.symm v) := hv.map e.symm.toMonoidHom
  obtain ⟨c, hc, hC⟩ := Polynomial.isUnit_iff.mp hP
  refine ⟨c, hc, ?_⟩
  calc
    algebraMap L A c = e (Polynomial.C c) := (e.commutes c).symm
    _ = v := by simpa only [AlgEquiv.apply_symm_apply] using congrArg e hC

variable {F : Type*} [Field F] [Algebra L F]

/-- Every unit of the entire actual parabola coordinate quotient
is a nonzero original-field constant in that actual quotient. -/
theorem parabola_coordinate_quotient_unit_is_constant
    (x : Fin 4 → F) (hx : LiesInAffineParabola (L := L) x)
    (v : MvPolynomial (Fin 4) L ⧸ fiberVanishingIdeal (L := L) x) (hv : IsUnit v) :
    ∃ c : L, c ≠ 0 ∧ algebraMap L (MvPolynomial (Fin 4) L ⧸ fiberVanishingIdeal (L := L) x) c = v := by
  obtain ⟨e⟩ := parabola_coordinate_quotient_polynomial_equiv x hx
  obtain ⟨c, hc, hvalue⟩ := polynomial_algebra_equiv_unit_is_coefficient e v hv
  exact ⟨c, hc.ne_zero, hvalue⟩

/-- An original polynomial whose class is invertible on the actual
parabola has an actual nonzero constant value in the original source field. -/
theorem parabola_polynomial_unit_mod_relations_constant
    (x : Fin 4 → F) (hx : LiesInAffineParabola (L := L) x)
    (P : MvPolynomial (Fin 4) L)
    (hP : IsUnit (Ideal.Quotient.mk (fiberVanishingIdeal (L := L) x) P)) :
    ∃ c : L, c ≠ 0 ∧ aeval x P = algebraMap L F c := by
  obtain ⟨c, hc, hvalue⟩ := parabola_coordinate_quotient_unit_is_constant x hx _ hP
  refine ⟨c, hc, ?_⟩
  let f : (MvPolynomial (Fin 4) L ⧸ fiberVanishingIdeal (L := L) x) →ₐ[L] F :=
    Ideal.kerLiftAlg (aeval x : MvPolynomial (Fin 4) L →ₐ[L] F)
  calc
    aeval x P = f (Ideal.Quotient.mk (fiberVanishingIdeal (L := L) x) P) :=
      (Ideal.kerLiftAlg_mk (aeval x : MvPolynomial (Fin 4) L →ₐ[L] F) P).symm
    _ = f (algebraMap L (MvPolynomial (Fin 4) L ⧸ fiberVanishingIdeal (L := L) x) c) :=
      congrArg f hvalue.symm
    _ = algebraMap L F c := f.commutes c

end DimensionFourDependence
