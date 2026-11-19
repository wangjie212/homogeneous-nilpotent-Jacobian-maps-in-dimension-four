import DimensionFourDependence.ResidueParameterField

/-! # The actual residue-parameter field actions preserve original constants -/

namespace DimensionFourDependence

variable {k B : Type*} [Field k] [CommRing B] [IsLocalRing B] [Algebra k B]

/-- The original rational parameter maps to the specified local coordinate. -/
theorem residueParameterFieldHom_X
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) :
    residueParameterFieldHom u hu RatFunc.X = u := by
  rw [← RatFunc.algebraMap_X, residueParameterFieldHom_polynomial, Polynomial.aeval_X]

/-- The actual regular rational coefficient-field action on the local ring. -/
@[instance_reducible]
noncomputable def residueParameterFieldAlgebra
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) : Algebra (RatFunc k) B :=
  (residueParameterFieldHom u hu).toRingHom.toAlgebra

/-- The regular rational coefficient-field action retains the original constants. -/
theorem residueParameterFieldAlgebra_scalarTower
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) :
    letI : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
    IsScalarTower k (RatFunc k) B := by
  letI : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
  exact IsScalarTower.of_algebraMap_eq (fun c => (residueParameterFieldHom u hu).commutes c |>.symm)

variable {L : Type*} [Field L] [Algebra B L] [Algebra k L] [IsScalarTower k B L]

/-- The same actual coefficient field acts on the target function field
through its original local-ring inclusion. -/
@[instance_reducible]
noncomputable def residueParameterTargetFieldAlgebra
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) : Algebra (RatFunc k) L :=
  ((algebraMap B L).comp (residueParameterFieldHom u hu).toRingHom).toAlgebra

/-- These two actual coefficient-field actions agree through the
given local-ring inclusion into its function field. -/
theorem residueParameterTargetFieldAlgebra_scalarTower
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) :
    letI : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
    letI : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
    IsScalarTower (RatFunc k) B L := by
  letI : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
  letI : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  exact IsScalarTower.of_algebraMap_eq (by intro c; rfl)

/-- The actual coefficient-field action in the target function field
preserves the original ground-field action. -/
theorem residueParameterTargetFieldAlgebra_base_scalarTower
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u)) :
    letI : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
    IsScalarTower k (RatFunc k) L := by
  letI : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap k L c = algebraMap B L (residueParameterFieldHom u hu (algebraMap k (RatFunc k) c))
  rw [(residueParameterFieldHom u hu).commutes, ← IsScalarTower.algebraMap_apply k B L]

end DimensionFourDependence
