import DimensionFourDependence.AffineLevelParameterField
import DimensionFourDependence.ClosedGaussCoordinateIntegrality
import DimensionFourDependence.ScalarExtensionRank
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Geometric integrality of the actual generic affine level

Relative algebraic closedness of the actual parameter field makes the
coordinate quotient remain integral under every algebraic coefficient
extension. The exact affine relation ideal identifies this quotient with
the literal equation P-t, without additional relations or components.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- Differentiating the actual affine level equation differentiates the
original polynomial and then extends its coefficients to K(t). -/
theorem actualAffineLevelEquation_pderiv
    (t : F) (P : MvPolynomial (Fin n) K) (i : Fin n) :
    pderiv i (actualAffineLevelEquation t P) =
      MvPolynomial.map (algebraMap K (IntermediateField.adjoin K {t})) (pderiv i P) := by
  simp [actualAffineLevelEquation, pderiv_map]

/-- A nonzero original partial derivative keeps the actual level equation
nonzero over every further coefficient field. -/
theorem actualAffineLevelEquation_map_ne_zero_of_pderiv
    (t : F) (P : MvPolynomial (Fin n) K) (i : Fin n) (hi : pderiv i P ≠ 0)
    (E : Type*) [Field E] [Algebra (IntermediateField.adjoin K {t}) E] :
    MvPolynomial.map (algebraMap (IntermediateField.adjoin K {t}) E)
      (actualAffineLevelEquation t P) ≠ 0 := by
  intro hz
  have hd := congrArg (pderiv i) hz
  rw [pderiv_map, actualAffineLevelEquation_pderiv, map_zero] at hd
  have houter := MvPolynomial.map_injective (σ := Fin n)
    (algebraMap (IntermediateField.adjoin K {t}) E)
    (algebraMap (IntermediateField.adjoin K {t}) E).injective
  have hinner := MvPolynomial.map_injective (σ := Fin n)
    (algebraMap K (IntermediateField.adjoin K {t}))
    (algebraMap K (IntermediateField.adjoin K {t})).injective
  exact hi (hinner ((houter (hd.trans (map_zero _).symm)).trans (map_zero _).symm))

variable [CharZero K]

/-- Every algebraic extension of the actual relatively closed parameter
field preserves the domain defined by the literal affine equation P-t. -/
theorem actual_affine_level_geometrically_integral
    (t : F) (ht : Transcendental K t) (x : Fin n → F)
    (hx : AlgebraicIndependent K x) (P : MvPolynomial (Fin n) K)
    (hvalue : t = aeval x P)
    (hclosed : algebraicClosure (IntermediateField.adjoin K {t}) F = ⊥)
    (E : Type*) [Field E] [Algebra (IntermediateField.adjoin K {t}) E]
    [Algebra.IsAlgebraic (IntermediateField.adjoin K {t}) E] :
    IsDomain (MvPolynomial (Fin n) E ⧸ Ideal.span
      {MvPolynomial.map (algebraMap (IntermediateField.adjoin K {t}) E)
        (actualAffineLevelEquation t P)}) := by
  let C := IntermediateField.adjoin K {t}
  let : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  let J := fiberVanishingIdeal (L := C) x
  let : IsDomain ((MvPolynomial (Fin n) C ⧸ J) ⊗[C] E) :=
    fiber_coordinate_quotient_algebraic_base_change_isDomain hclosed x
  let c := Algebra.TensorProduct.comm C E (MvPolynomial (Fin n) C ⧸ J)
  let : IsDomain (E ⊗[C] (MvPolynomial (Fin n) C ⧸ J)) :=
    Function.Injective.isDomain c c.injective
  let b := polynomialQuotientBaseChangeEquiv E J
  have hJ : extendCoefficientIdeal E J = Ideal.span
      {MvPolynomial.map (algebraMap C E) (actualAffineLevelEquation t P)} := by
    rw [show J = Ideal.span {actualAffineLevelEquation t P} from
      actual_affine_level_parameter_field_relation_ideal t ht x hx P hvalue]
    simp only [extendCoefficientIdeal, Ideal.map_span, Set.image_singleton]
  rw [← hJ]
  exact Function.Injective.isDomain b.symm b.symm.injective

/-- A nonzero original partial derivative turns geometric integrality of
the actual affine level into irreducibility of its exact defining equation. -/
theorem actual_affine_level_geometrically_irreducible
    (t : F) (ht : Transcendental K t) (x : Fin n → F)
    (hx : AlgebraicIndependent K x) (P : MvPolynomial (Fin n) K)
    (hvalue : t = aeval x P)
    (hclosed : algebraicClosure (IntermediateField.adjoin K {t}) F = ⊥)
    (i : Fin n) (hi : pderiv i P ≠ 0)
    (E : Type*) [Field E] [Algebra (IntermediateField.adjoin K {t}) E]
    [Algebra.IsAlgebraic (IntermediateField.adjoin K {t}) E] :
    Irreducible (MvPolynomial.map (algebraMap (IntermediateField.adjoin K {t}) E)
      (actualAffineLevelEquation t P)) := by
  have hn := actualAffineLevelEquation_map_ne_zero_of_pderiv t P i hi E
  exact ((Ideal.span_singleton_prime hn).mp ((Ideal.Quotient.isDomain_iff_prime _).mp
    (actual_affine_level_geometrically_integral t ht x hx P hvalue hclosed E))).irreducible

end DimensionFourDependence
