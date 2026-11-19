import DimensionFourDependence.ResidueParameterAlgebra
import DimensionFourDependence.TwoParameterProjection
import DimensionFourDependence.LocalParameterProjectionField

/-! # Actual independent projection coordinates from a residue parameter

The regular residue parameter and the vanishing coordinate construct
the projection field. Its two canonical variables map to those exact
original local coordinate values in the actual function field.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k B L : Type*} [Field k]
  [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra k B]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra k L] [IsScalarTower k B L]

/-- The actual two-coordinate projection field action is constructed
from the original residue parameter and original vanishing coordinate. -/
@[instance_reducible]
noncomputable def residueCoordinateProjectionAlgebra
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    Algebra (FractionRing (Polynomial (RatFunc k))) L := by
  letI : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
  letI : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  letI : IsScalarTower (RatFunc k) B L := residueParameterTargetFieldAlgebra_scalarTower (L := L) u hu
  exact localParameterProjectionFieldAlgebra (k := RatFunc k) (L := L) z hz0 hz

/-- The actual projection field retains the original ground-field action. -/
theorem residueCoordinateProjection_base_scalarTower
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    letI : Algebra (FractionRing (Polynomial (RatFunc k))) L :=
      residueCoordinateProjectionAlgebra (L := L) u hu z hz0 hz
    IsScalarTower k (FractionRing (Polynomial (RatFunc k))) L := by
  letI : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
  letI : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  letI : IsScalarTower (RatFunc k) B L := residueParameterTargetFieldAlgebra_scalarTower (L := L) u hu
  letI : IsScalarTower k (RatFunc k) L := residueParameterTargetFieldAlgebra_base_scalarTower (L := L) u hu
  letI : Algebra (FractionRing (Polynomial (RatFunc k))) L :=
    residueCoordinateProjectionAlgebra (L := L) u hu z hz0 hz
  let : IsScalarTower (RatFunc k) (FractionRing (Polynomial (RatFunc k))) L :=
    IsScalarTower.of_algebraMap_eq (fun c =>
      (localParameterProjectionFieldHom (k := RatFunc k) (L := L) z hz0 hz).commutes c |>.symm)
  exact IsScalarTower.to₁₃₄ k (RatFunc k) (FractionRing (Polynomial (RatFunc k))) L

/-- The constructed independent projection coordinates have exactly
the two specified original coordinate values in the target function field. -/
theorem residueCoordinateProjection_coordinates
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    letI : Algebra (FractionRing (Polynomial (RatFunc k))) L :=
      residueCoordinateProjectionAlgebra (L := L) u hu z hz0 hz
    ∀ i : Option Unit,
      algebraMap (FractionRing (Polynomial (RatFunc k))) L (twoParameterProjectionCoordinates k i) =
        i.elim (algebraMap B L z) (fun _ => algebraMap B L u) := by
  letI : Algebra (RatFunc k) B := residueParameterFieldAlgebra u hu
  letI : Algebra (RatFunc k) L := residueParameterTargetFieldAlgebra (L := L) u hu
  letI : IsScalarTower (RatFunc k) B L := residueParameterTargetFieldAlgebra_scalarTower (L := L) u hu
  letI : Algebra (FractionRing (Polynomial (RatFunc k))) L :=
    residueCoordinateProjectionAlgebra (L := L) u hu z hz0 hz
  intro i
  cases i with
  | none =>
    change localParameterProjectionFieldHom (k := RatFunc k) (L := L) z hz0 hz
      (algebraMap (Polynomial (RatFunc k)) (FractionRing (Polynomial (RatFunc k))) Polynomial.X) = _
    rw [localParameterProjectionFieldHom_polynomial, Polynomial.aeval_X]
    rfl
  | some j =>
    change localParameterProjectionFieldHom (k := RatFunc k) (L := L) z hz0 hz
      (algebraMap (RatFunc k) (FractionRing (Polynomial (RatFunc k))) RatFunc.X) = _
    rw [(localParameterProjectionFieldHom (k := RatFunc k) (L := L) z hz0 hz).commutes]
    change algebraMap B L (residueParameterFieldHom u hu RatFunc.X) = algebraMap B L u
    rw [residueParameterFieldHom_X]

/-- The two actual original coordinate values are independent whenever
the first has transcendental residue and the second vanishes nontrivially. -/
theorem residue_and_vanishing_coordinates_algebraicIndependent
    (u : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    AlgebraicIndependent k (fun i : Option Unit =>
      i.elim (algebraMap B L z) (fun _ => algebraMap B L u)) := by
  let T := FractionRing (Polynomial (RatFunc k))
  letI : Algebra T L := residueCoordinateProjectionAlgebra (L := L) u hu z hz0 hz
  letI : IsScalarTower k T L := residueCoordinateProjection_base_scalarTower (L := L) u hu z hz0 hz
  let j : T →ₐ[k] L := IsScalarTower.toAlgHom k T L
  have h := (twoParameterProjectionCoordinates_algebraicIndependent k).map (f := j) j.injective.injOn
  change AlgebraicIndependent k (fun i => algebraMap T L (twoParameterProjectionCoordinates k i)) at h
  have hvalues : (fun i => algebraMap T L (twoParameterProjectionCoordinates k i)) =
      (fun i : Option Unit => i.elim (algebraMap B L z) (fun _ => algebraMap B L u)) :=
    funext (residueCoordinateProjection_coordinates (L := L) u hu z hz0 hz)
  rw [hvalues] at h
  exact h

end DimensionFourDependence
