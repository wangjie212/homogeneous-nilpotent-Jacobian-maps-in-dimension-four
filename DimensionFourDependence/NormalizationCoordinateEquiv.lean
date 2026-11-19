import DimensionFourDependence.NormalizationRing

/-! # Normalization under an actual affine coordinate isomorphism

An isomorphism of affine source rings extends to their actual fraction
fields and integral closures. The resulting normalization isomorphism
is induced by those source maps, rather than chosen independently.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {A B T : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [CommRing T] [Algebra A T] [IsFractionRing A T]

/-- Identifying an affine ring with its actual coordinate ring identifies
its function-field integral closure with the canonical coordinate normalization. -/
noncomputable def normalizationCoordinateEquiv (e : A ≃+* B) :
    integralClosure A T ≃+* normalizationRing B := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let bFractionAction : Algebra B (FractionRing B) := OreLocalization.instAlgebra
  let : Algebra B (FractionRing B) := bFractionAction
  let : SMul B (FractionRing B) := bFractionAction.toSMul
  let fractionAction : Algebra A (FractionRing B) :=
    ((algebraMap B (FractionRing B)).comp e.toRingHom).toAlgebra
  let : Algebra A (FractionRing B) := fractionAction
  let : SMul A (FractionRing B) := fractionAction.toSMul
  let : IsScalarTower A B (FractionRing B) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let eA : A ≃ₐ[A] B := { e with commutes' := fun _ => rfl }
  let φ : T ≃ₐ[A] FractionRing B := IsFractionRing.algEquivOfAlgEquiv eA
  let : Algebra.IsIntegral A B := Algebra.isIntegral_of_surjective e.surjective
  let β : integralClosure A (FractionRing B) ≃+* integralClosure B (FractionRing B) :=
    { toFun := fun z => ⟨z.val, z.property.tower_top⟩
      invFun := fun z => ⟨z.val, isIntegral_trans (R := A) (A := B) _ z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  exact φ.mapIntegralClosure.toRingEquiv.trans β

omit [IsDomain A] [IsDomain B] in
/-- The induced normalization isomorphism preserves the entire original
affine source ring through the specified coordinate isomorphism. -/
theorem normalizationCoordinateEquiv_algebraMap (e : A ≃+* B) (r : A) :
    normalizationCoordinateEquiv (T := T) e (algebraMap A (integralClosure A T) r) =
      algebraMap B (normalizationRing B) (e r) := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let bFractionAction : Algebra B (FractionRing B) := OreLocalization.instAlgebra
  let : Algebra B (FractionRing B) := bFractionAction
  let : SMul B (FractionRing B) := bFractionAction.toSMul
  let fractionAction : Algebra A (FractionRing B) :=
    ((algebraMap B (FractionRing B)).comp e.toRingHom).toAlgebra
  let : Algebra A (FractionRing B) := fractionAction
  let : SMul A (FractionRing B) := fractionAction.toSMul
  let : IsScalarTower A B (FractionRing B) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let eA : A ≃ₐ[A] B := { e with commutes' := fun _ => rfl }
  apply Subtype.ext
  change IsFractionRing.algEquivOfAlgEquiv eA (algebraMap A T r) =
    algebraMap B (FractionRing B) (eA r)
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap eA r

end DimensionFourDependence
