import DimensionFourDependence.IndependentProjectionField
import DimensionFourDependence.ResidueParameterAlgebra

/-! # The iterated projection field from the actual local residue parameter

The first coordinate has transcendental residue and thus embeds its whole
rational function field in the actual local ring. Independence of the two
original function-field coordinates then extends the second polynomial
evaluation to the full iterated rational projection field.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {k B L : Type*} [Field k] [CommRing B] [IsLocalRing B] [Algebra k B]
  [Field L] [Algebra B L] [Algebra k L] [IsScalarTower k B L]

omit [Algebra k L] [IsScalarTower k B L] in
/-- The actual regular residue parameter retains its original value in
the target function field. -/
theorem residueParameterTargetFieldAlgebra_X
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) :
    let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
    algebraMap (RatFunc k) L RatFunc.X = algebraMap B L u := by
  let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  change algebraMap B L (residueParameterFieldHom u hu RatFunc.X) = algebraMap B L u
  rw [residueParameterFieldHom_X]

/-- The actual local residue parameter and independent original
coordinate construct the complete iterated rational projection-field
embedding into the specified function field. -/
noncomputable def independentResidueProjectionFieldHom
    (u w : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (h : AlgebraicIndependent k ![algebraMap B L u, algebraMap B L w]) :
    let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
    RatFunc (RatFunc k) →ₐ[RatFunc k] L := by
  let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  let : IsScalarTower k (RatFunc k) L :=
    residueParameterTargetFieldAlgebra_base_scalarTower (L := L) u hu
  exact independentProjectionFieldHom _ _ h (residueParameterTargetFieldAlgebra_X (L := L) u hu)

/-- Every actual outer polynomial retains its original value in the
function field under the constructed iterated projection embedding. -/
theorem independentResidueProjectionFieldHom_polynomial
    (u w : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (h : AlgebraicIndependent k ![algebraMap B L u, algebraMap B L w])
    (P : Polynomial (RatFunc k)) :
    let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
    independentResidueProjectionFieldHom u w hu h
      (algebraMap (Polynomial (RatFunc k)) (RatFunc (RatFunc k)) P) =
        Polynomial.aeval (algebraMap B L w) P := by
  let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  let : IsScalarTower k (RatFunc k) L :=
    residueParameterTargetFieldAlgebra_base_scalarTower (L := L) u hu
  exact independentProjectionFieldHom_polynomial _ _ h
    (residueParameterTargetFieldAlgebra_X (L := L) u hu) P

/-- The actual iterated projection action on the specified function field. -/
@[instance_reducible]
noncomputable def independentResidueProjectionFieldAlgebra
    (u w : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (h : AlgebraicIndependent k ![algebraMap B L u, algebraMap B L w]) :
    Algebra (RatFunc (RatFunc k)) L := by
  let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  exact (independentResidueProjectionFieldHom u w hu h).toRingHom.toAlgebra

/-- The actual outer rational projection variable is the original local
coordinate, through its specified inclusion in the function field. -/
theorem independentResidueProjectionFieldAlgebra_X
    (u w : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (h : AlgebraicIndependent k ![algebraMap B L u, algebraMap B L w]) :
    let : Algebra (RatFunc (RatFunc k)) L := independentResidueProjectionFieldAlgebra u w hu h
    algebraMap (RatFunc (RatFunc k)) L RatFunc.X = algebraMap B L w := by
  let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  let : Algebra (RatFunc (RatFunc k)) L := independentResidueProjectionFieldAlgebra u w hu h
  rw [← RatFunc.algebraMap_X]
  change independentResidueProjectionFieldHom u w hu h
    (algebraMap (Polynomial (RatFunc k)) (RatFunc (RatFunc k)) Polynomial.X) = _
  rw [independentResidueProjectionFieldHom_polynomial, Polynomial.aeval_X]

/-- Both actual inner and outer projection field actions agree, with
the inner action still regular in the original local ring. -/
theorem independentResidueProjectionFieldAlgebra_scalarTower
    (u w : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (h : AlgebraicIndependent k ![algebraMap B L u, algebraMap B L w]) :
    let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
    let : Algebra (RatFunc (RatFunc k)) L := independentResidueProjectionFieldAlgebra u w hu h
    IsScalarTower (RatFunc k) (RatFunc (RatFunc k)) L := by
  let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  let : IsScalarTower k (RatFunc k) L :=
    residueParameterTargetFieldAlgebra_base_scalarTower (L := L) u hu
  exact independentProjectionFieldAlgebra_scalarTower _ _ h
    (residueParameterTargetFieldAlgebra_X (L := L) u hu)

/-- The iterated projection action retains the entire original constant field. -/
theorem independentResidueProjectionFieldAlgebra_original_scalarTower
    (u w : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (h : AlgebraicIndependent k ![algebraMap B L u, algebraMap B L w]) :
    let : Algebra (RatFunc (RatFunc k)) L := independentResidueProjectionFieldAlgebra u w hu h
    IsScalarTower k (RatFunc (RatFunc k)) L := by
  let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  let : IsScalarTower k (RatFunc k) L :=
    residueParameterTargetFieldAlgebra_base_scalarTower (L := L) u hu
  exact independentProjectionFieldAlgebra_original_scalarTower _ _ h
    (residueParameterTargetFieldAlgebra_X (L := L) u hu)

/-- The inner rational projection parameter has the original residue
coordinate value in the actual function field. -/
theorem independentResidueProjectionFieldAlgebra_inner_X
    (u w : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (h : AlgebraicIndependent k ![algebraMap B L u, algebraMap B L w]) :
    let : Algebra (RatFunc (RatFunc k)) L := independentResidueProjectionFieldAlgebra u w hu h
    algebraMap (RatFunc (RatFunc k)) L
      (algebraMap (RatFunc k) (RatFunc (RatFunc k)) RatFunc.X) = algebraMap B L u := by
  let : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  let : IsScalarTower k (RatFunc k) L :=
    residueParameterTargetFieldAlgebra_base_scalarTower (L := L) u hu
  exact independentProjectionFieldHom_inner_X _ _ h
    (residueParameterTargetFieldAlgebra_X (L := L) u hu)

end DimensionFourDependence
