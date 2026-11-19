import DimensionFourDependence.GenericPointAffineField
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Finite global normalization of finite-type integral schemes in characteristic zero

Every affine inverse-open ring in the actual generic-point normalization
is its source affine ring's fraction field. The proved finite-type
normalization theorem therefore supplies all affine finite closures.
The target-local finiteness criterion proves the global morphism finite.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type u} [Field K] [CharZero K]
  (X : Scheme.{u}) [IsIntegral X] (s : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType s]

include s in
/-- Finiteness of the actual global normalization is derived from
finite type over the original characteristic-zero coefficient field. -/
theorem integralSchemeNormalizationMap_finite_of_finiteType :
    IsFinite (integralSchemeNormalizationMap X) := by
  apply relative_normalization_finite_of_affine_closures_finite
    (integralSchemeGenericPointMorphism X)
  intro U
  let A := Γ(X, U.1)
  let T := Γ(Spec X.functionField, integralSchemeGenericPointMorphism X ⁻¹ᵁ U.1)
  let : Algebra A T := ((integralSchemeGenericPointMorphism X).app U.1).hom.toAlgebra
  by_cases hU : Nonempty U.1
  · let : Nonempty U.1 := hU
    let B := Γ(Spec (CommRingCat.of K), ⊤)
    let eb : B ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
    let : Field B := (eb.toMulEquiv.isField (Field.toIsField K)).toField
    let : CharZero B := ⟨fun m n h => by
      apply Nat.cast_injective (R := K)
      simpa only [map_natCast] using congrArg eb h⟩
    let ρ : B →+* A := (s.appLE ⊤ U.1 (by simp)).hom
    let : Algebra B A := ρ.toAlgebra
    let : Algebra.FiniteType B A :=
      s.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)
    let et : T ≃+* X.functionField := genericPointOpenSectionEquiv X U.1
    let : Field T := (et.toMulEquiv.isField (Field.toIsField X.functionField)).toField
    let : IsFractionRing A T := generic_point_affine_open_sections_isFractionRing X U.1 U.2
    exact finite_normalization_of_finiteType (K := B) (A := A) (F := T)
  · have hUb : U.1 = ⊥ := by
      apply SetLike.ext
      intro z
      simp only [Opens.mem_bot, iff_false]
      exact fun hz => hU ⟨⟨z, hz⟩⟩
    let : Subsingleton A :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hUb)
    have h01 : (0 : T) = 1 := by
      calc
        0 = algebraMap A T 0 := (map_zero _).symm
        _ = algebraMap A T 1 := congrArg (algebraMap A T) (Subsingleton.elim _ _)
        _ = 1 := map_one _
    let : Subsingleton T := subsingleton_of_zero_eq_one h01
    infer_instance

end DimensionFourDependence
