import DimensionFourDependence.ResidueProjectionPolynomialActions
import DimensionFourDependence.RationalInfinityTargetAction

/-! # All actions of the actual independent residue projection agree

This packages the explicit regular parameter, polynomial, iterated
rational and infinity actions, including their original coordinate values.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k B L : Type*} [Field k] [CommRing B] [IsLocalRing B] [Algebra k B]
  [Field L] [Algebra B L] [Algebra k L] [IsScalarTower k B L]

/-- Compatibility and actual values of all the constructed projection
actions. In particular the coefficient field acts on the original local
ring, and both the polynomial and infinity rings act through the same
iterated rational function field in the original function field. -/
def residueProjectionActionsCompatible
    (u w : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (h : AlgebraicIndependent k ![algebraMap B L u, algebraMap B L w]) : Prop :=
  let : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
  let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
  let : Algebra (Polynomial (RatFunc k)) L := residueProjectionPolynomialTargetAlgebra (L := L) u hu w
  let : Algebra (RatFunc (RatFunc k)) L := independentResidueProjectionFieldAlgebra u w hu h
  let : Algebra (rationalInfinityRing (RatFunc k)) L := rationalInfinityTargetAlgebra (k := RatFunc k)
  IsScalarTower k (RatFunc k) B ∧
  IsScalarTower (RatFunc k) B L ∧
  IsScalarTower k (RatFunc (RatFunc k)) L ∧
  IsScalarTower k (Polynomial (RatFunc k)) B ∧
  IsScalarTower k (Polynomial (RatFunc k)) L ∧
  IsScalarTower (Polynomial (RatFunc k)) B L ∧
  IsScalarTower (Polynomial (RatFunc k)) (RatFunc (RatFunc k)) L ∧
  IsScalarTower (rationalInfinityRing (RatFunc k)) (RatFunc (RatFunc k)) L ∧
  algebraMap (RatFunc (RatFunc k)) L RatFunc.X = algebraMap B L w ∧
  algebraMap (RatFunc (RatFunc k)) L
    (algebraMap (RatFunc k) (RatFunc (RatFunc k)) RatFunc.X) = algebraMap B L u ∧
  algebraMap (Polynomial (RatFunc k)) B Polynomial.X = w

/-- Every independent original pair whose first residue is
transcendental supplies all the compatible actual projection actions. -/
theorem residue_projection_actions_compatible
    (u w : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (h : AlgebraicIndependent k ![algebraMap B L u, algebraMap B L w]) :
    residueProjectionActionsCompatible u w hu h := by
  let : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
  let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  let : Algebra (Polynomial (RatFunc k)) B := residueProjectionPolynomialAlgebra u hu w
  let : Algebra (Polynomial (RatFunc k)) L := residueProjectionPolynomialTargetAlgebra (L := L) u hu w
  let : Algebra (RatFunc (RatFunc k)) L := independentResidueProjectionFieldAlgebra u w hu h
  let : Algebra (rationalInfinityRing (RatFunc k)) L := rationalInfinityTargetAlgebra (k := RatFunc k)
  exact ⟨residueParameterFieldAlgebra_scalarTower u hu,
    residueParameterTargetFieldAlgebra_scalarTower (L := L) u hu,
    independentResidueProjectionFieldAlgebra_original_scalarTower u w hu h,
    residueProjectionPolynomialAlgebra_original_scalarTower u hu w,
    residueProjectionPolynomialTargetAlgebra_original_scalarTower (L := L) u hu w,
    residueProjectionPolynomialTargetAlgebra_source_scalarTower (L := L) u hu w,
    independentResidueProjectionFieldAlgebra_polynomial_scalarTower u w hu h,
    rationalInfinityTargetAlgebra_scalarTower (k := RatFunc k) (L := L),
    independentResidueProjectionFieldAlgebra_X u w hu h,
    independentResidueProjectionFieldAlgebra_inner_X u w hu h,
    residueProjectionPolynomialAlgebra_X u hu w⟩

/-- Reordering an independent pair puts either selected coordinate
first while retaining the other coordinate in the second slot. -/
theorem algebraicIndependent_pair_selected_first
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    (z : Fin 2 → L) (h : AlgebraicIndependent k z) (j : Fin 2) :
    AlgebraicIndependent k ![z j, z (Equiv.swap (0 : Fin 2) j 1)] := by
  classical
  have hc := h.comp (Equiv.swap (0 : Fin 2) j) (Equiv.swap (0 : Fin 2) j).injective
  change AlgebraicIndependent k (fun i => z (Equiv.swap (0 : Fin 2) j i)) at hc
  have heq : (fun i => z (Equiv.swap (0 : Fin 2) j i)) =
      ![z j, z (Equiv.swap (0 : Fin 2) j 1)] := by
    funext i
    fin_cases i <;> simp
  exact Eq.mp (congrArg (fun f : Fin 2 → L => AlgebraicIndependent k f) heq) hc

end DimensionFourDependence
