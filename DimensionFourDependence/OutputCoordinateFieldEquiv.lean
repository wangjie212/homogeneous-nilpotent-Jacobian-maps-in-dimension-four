import DimensionFourDependence.FiberCoordinateRing
import DimensionFourDependence.GenericOutputPoint
import DimensionFourDependence.RationalJacobianCriterion
import DimensionFourDependence.ImageHypersurface

/-! # Actual output fields from their exact polynomial relations

The field of output coordinates is the fraction field of their prime
coordinate quotient. Equal polynomial relation ideals therefore give
isomorphic output fields, preserving their transcendence degrees.
-/

namespace DimensionFourDependence

variable {K F G : Type*} [Field K] [Field F] [Field G]
variable [Algebra K F] [Algebra K G] {n : ℕ}

/-- The prime coordinate quotient has exactly the generated output field
as its actual fraction field. -/
noncomputable def outputCoordinateFunctionFieldEquiv (x : Fin n → F) :
    FractionRing (MvPolynomial (Fin n) K ⧸ fiberVanishingIdeal (L := K) x) ≃ₐ[K]
      fullOutputField (K := K) x :=
  (IsFractionRing.algEquivOfAlgEquiv
    (K := FractionRing (MvPolynomial (Fin n) K ⧸ fiberVanishingIdeal (L := K) x))
    (L := FractionRing (fiberCoordinateAlgebra (L := K) x))
    (fiberCoordinateQuotientEquiv (L := K) x)).trans
      ((fiberCoordinateFractionHom (L := K) x).equivFieldRange.trans
        (IntermediateField.equivOfEq (fiberCoordinateFractionHom_fieldRange (L := K) x)))

/-- Two actual coordinate points with the same original-field relations
have isomorphic generated output fields. -/
noncomputable def outputFieldEquivOfRelations (x : Fin n → F) (y : Fin n → G)
    (hrel : fiberVanishingIdeal (L := K) x = fiberVanishingIdeal (L := K) y) :
    fullOutputField (K := K) x ≃ₐ[K] fullOutputField (K := K) y :=
  (outputCoordinateFunctionFieldEquiv (K := K) x).symm.trans
    ((IsFractionRing.algEquivOfAlgEquiv (Ideal.quotientEquivAlgOfEq K hrel)).trans
      (outputCoordinateFunctionFieldEquiv (K := K) y))

omit [Field F] [Field G] [Algebra K F] [Algebra K G] in
/-- The original polynomial output field has the actual polynomial Jacobian rank. -/
theorem polynomialOutputField_trdeg_eq_rank [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) :
    Algebra.trdeg K (polynomialOutputField H) = polyRank (jac H) := by
  have he := rationalJacobian_rank_eq_output_trdeg
    (fun i => algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) (H i))
  rw [rationalJacobian_polynomial H] at he
  exact he

end DimensionFourDependence
