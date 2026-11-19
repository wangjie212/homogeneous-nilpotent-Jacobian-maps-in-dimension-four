import DimensionFourDependence.TransverseParameterIndependence
import DimensionFourDependence.RationalClosedGaussCover

/-! # Source independence over the actual closed Gauss parameter field

The actual reduced homogeneous parameter representation identifies its
generated field with the original relatively closed Gauss field. Genuine
vertex dependence therefore makes the three original transverse source
coordinates independent over that entire actual parameter field.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- A genuine vertex-dependent original reduced Gauss pencil
constructs transverse source independence over its own actual closed
parameter field, with no auxiliary coefficient-field model. -/
theorem actual_closed_gauss_vertex_pencil_transverse_source_independent
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3)) :
    AlgebraicIndependent (closedGaussParameterField H I)
      (fun i : Fin 3 => rationalCoordinate (K := K) i.castSucc) := by
  have hi := reduced_vertex_pencil_transverse_coordinates_independent_over_parameter_field
    p q hp0 hq0 hrel hp hq hvertex
  have he : IntermediateField.adjoin K
      {algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q} =
      closedGaussParameterField H I := by
    rw [← hparameter, closedGaussParameterSourceHom_X_adjoin]
  rw [he] at hi
  exact hi

end DimensionFourDependence
