import DimensionFourDependence.AdjoinInverseLocalization
import DimensionFourDependence.NormalizationRing
import Mathlib.RingTheory.Localization.Integral

/-! # Normalization compatibility on principal chart overlaps

The integral closure of the inverse-adjoining overlap is the localization
of the original integral closure. Both rings and their map are realized
inside the actual same ambient field.
-/

namespace DimensionFourDependence

variable {A F : Type*} [CommRing A] [Field F] [Algebra A F] [FaithfulSMul A F]

/-- The actual inclusion of the original integral closure into the
integral closure on its principal overlap. -/
noncomputable def integralClosurePrincipalOverlapHom (r : A) :
    integralClosure A F →+* integralClosure (adjoinInverseAlgebra (F := F) r) F where
  toFun x := ⟨x.val, x.property.tower_top⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

omit [FaithfulSMul A F] in
/-- The overlap map is literally the same rational function in the
original ambient field. -/
theorem integralClosurePrincipalOverlapHom_coe (r : A) (x : integralClosure A F) :
    ((integralClosurePrincipalOverlapHom (F := F) r x :
      integralClosure (adjoinInverseAlgebra (F := F) r) F) : F) = x := rfl

/-- Integral closure on the actual principal overlap is the principal
localization of the original integral closure. -/
theorem integralClosure_principal_overlap_isLocalization (r : A) (hr : algebraMap A F r ≠ 0) :
    letI : Algebra (integralClosure A F) (integralClosure (adjoinInverseAlgebra (F := F) r) F) :=
      (integralClosurePrincipalOverlapHom (F := F) r).toAlgebra
    IsLocalization.Away (algebraMap A (integralClosure A F) r)
      (integralClosure (adjoinInverseAlgebra (F := F) r) F) := by
  let T := adjoinInverseAlgebra (F := F) r
  let N := integralClosure A F
  let NT := integralClosure T F
  let : IsScalarTower A T NT := IsScalarTower.of_algebraMap_eq (by intro a; rfl)
  let : IsScalarTower A NT F := IsScalarTower.of_algebraMap_eq (by intro a; rfl)
  let : Algebra N NT := (integralClosurePrincipalOverlapHom (F := F) r).toAlgebra
  let : IsScalarTower N NT F := IsScalarTower.of_algebraMap_eq (by intro x; rfl)
  let : IsScalarTower A N NT := IsScalarTower.of_algebraMap_eq (by intro a; rfl)
  let : IsLocalization.Away r T := adjoinInverseAlgebra_isLocalization r hr
  let : IsLocalization.Away (algebraMap A F r) F :=
    IsLocalization.away_of_isUnit_of_bijective F (isUnit_iff_ne_zero.mpr hr) Function.bijective_id
  exact IsLocalization.Away.integralClosure (S := F) (Rf := T) (Sf := F) r

end DimensionFourDependence
