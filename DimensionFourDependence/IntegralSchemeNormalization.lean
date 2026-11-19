import DimensionFourDependence.FiniteRelativeNormalization
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk

/-! # Global normalization in an integral scheme's actual function field

The generic point supplies the function-field morphism, with the qcqs
conditions derived from its field spectrum. Relative normalization then
glues the actual affine integral closures, gives an integral global
scheme and morphism, and factors that original function-field morphism.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable (X : Scheme.{u}) [IsIntegral X]

/-- The canonical morphism from the actual function field into its integral scheme. -/
noncomputable def integralSchemeGenericPointMorphism : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

/-- The function-field morphism has exactly the original generic point as image. -/
theorem integralSchemeGenericPointMorphism_range :
    Set.range (integralSchemeGenericPointMorphism X) = {genericPoint X} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint X.functionField :=
      Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
    rw [hz]
    exact Set.mem_singleton_iff.mpr Scheme.fromSpecStalk_closedPoint
  · rintro rfl
    exact ⟨IsLocalRing.closedPoint X.functionField, Scheme.fromSpecStalk_closedPoint⟩

/-- The original function-field morphism is dominant. -/
theorem integralSchemeGenericPointMorphism_isDominant :
    IsDominant (integralSchemeGenericPointMorphism X) := by
  constructor
  rw [denseRange_iff_closure_range, integralSchemeGenericPointMorphism_range]
  exact genericPoint_spec X

/-- The source field spectrum automatically supplies quasi-compactness. -/
theorem integralSchemeGenericPointMorphism_quasiCompact :
    QuasiCompact (integralSchemeGenericPointMorphism X) := by
  infer_instance

/-- The source field spectrum automatically supplies quasi-separatedness. -/
theorem integralSchemeGenericPointMorphism_quasiSeparated :
    QuasiSeparated (integralSchemeGenericPointMorphism X) := by
  infer_instance

/-- Global normalization in the original function field, with affine
overlap gluing provided by relative normalization. -/
noncomputable def integralSchemeNormalization : Scheme.{u} :=
  (integralSchemeGenericPointMorphism X).normalization

/-- The integral global normalization morphism back to the original scheme. -/
noncomputable def integralSchemeNormalizationMap : integralSchemeNormalization X ⟶ X :=
  (integralSchemeGenericPointMorphism X).fromNormalization

/-- The original function-field point on the actual global normalization. -/
noncomputable def integralSchemeNormalizationGenericPoint :
    Spec X.functionField ⟶ integralSchemeNormalization X :=
  (integralSchemeGenericPointMorphism X).toNormalization

/-- The normalization preserves the original function-field morphism. -/
theorem integralSchemeNormalization_factorization :
    integralSchemeNormalizationGenericPoint X ≫ integralSchemeNormalizationMap X =
      integralSchemeGenericPointMorphism X :=
  (integralSchemeGenericPointMorphism X).toNormalization_fromNormalization

/-- The constructed global normalization scheme is itself integral. -/
theorem integralSchemeNormalization_isIntegral : IsIntegral (integralSchemeNormalization X) := by
  unfold integralSchemeNormalization
  infer_instance

/-- Its map to the original scheme is integral. -/
theorem integralSchemeNormalizationMap_isIntegralHom :
    IsIntegralHom (integralSchemeNormalizationMap X) := by
  unfold integralSchemeNormalizationMap
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- Each inverse affine open is the actual integral closure appearing
in the normalization gluing, rather than an abstract chart hypothesis. -/
noncomputable def integralSchemeNormalizationAffineChart (U : X.affineOpens) :
    letI := ((integralSchemeGenericPointMorphism X).app U.1).hom.toAlgebra
    (integralSchemeNormalizationMap X ⁻¹ᵁ U.1).toScheme ≅
      Spec (CommRingCat.of (integralClosure Γ(X, U.1)
        Γ(Spec X.functionField, integralSchemeGenericPointMorphism X ⁻¹ᵁ U.1))) := by
  let f := integralSchemeGenericPointMorphism X
  exact IsOpenImmersion.isoOfRangeEq (f.fromNormalization ⁻¹ᵁ U.1).ι
    (f.normalizationOpenCover.f U)
    (by
      ext z
      constructor
      · rintro ⟨z, rfl⟩
        exact (f.fromNormalization_preimage U).le z.property
      · intro hz
        exact ⟨⟨z, (f.fromNormalization_preimage U).ge hz⟩, rfl⟩)

end DimensionFourDependence
