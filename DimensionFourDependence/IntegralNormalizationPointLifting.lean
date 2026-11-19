import DimensionFourDependence.IntegralSchemeNormalization
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-! # Point and specialization lifting in the actual global normalization -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

variable (X : Scheme.{u}) [IsIntegral X]

/-- The normalization in the actual scheme function field is dominant,
using its checked factorization of the original generic-point morphism. -/
theorem integralSchemeNormalizationMap_isDominant :
    IsDominant (integralSchemeNormalizationMap X) := by
  let : IsDominant (integralSchemeGenericPointMorphism X) :=
    integralSchemeGenericPointMorphism_isDominant X
  let : IsDominant
      (integralSchemeNormalizationGenericPoint X ≫ integralSchemeNormalizationMap X) := by
    rw [integralSchemeNormalization_factorization]
    infer_instance
  exact IsDominant.of_comp (integralSchemeNormalizationGenericPoint X) _

/-- Every point has a preimage on the actual normalization; no
normalization point or nonempty fiber is supplied as a hypothesis. -/
theorem integralSchemeNormalizationMap_surjective :
    Function.Surjective (integralSchemeNormalizationMap X) := by
  let : IsIntegralHom (integralSchemeNormalizationMap X) :=
    integralSchemeNormalizationMap_isIntegralHom X
  let : IsDominant (integralSchemeNormalizationMap X) :=
    integralSchemeNormalizationMap_isDominant X
  exact Scheme.Hom.surjective _

/-- A specialization from a given normalized generic point lifts
on that same branch, by closedness of the actual integral normalization. -/
theorem integralSchemeNormalizationMap_lifts_specialization
    (x : integralSchemeNormalization X) (y : X)
    (hxy : integralSchemeNormalizationMap X x ⤳ y) :
    ∃ z : integralSchemeNormalization X, x ⤳ z ∧ integralSchemeNormalizationMap X z = y := by
  let : IsIntegralHom (integralSchemeNormalizationMap X) :=
    integralSchemeNormalizationMap_isIntegralHom X
  have h := (integralSchemeNormalizationMap X).isClosedMap.specializingMap
  have hy : y ∈ closure {integralSchemeNormalizationMap X x} := hxy.mem_closure
  obtain ⟨z, hz, he⟩ := h.closure_singleton_subset x hy
  exact ⟨z, specializes_iff_mem_closure.mpr hz, he⟩

/-- A closed source embedding preserves the same branch while a
specialization in its ambient space lifts to the actual normalization. -/
theorem integralSchemeNormalization_lifts_ambient_specialization
    {Y : Scheme.{u}} (j : X ⟶ Y) [IsClosedImmersion j]
    (x : X) (y : Y) (hxy : j x ⤳ y) :
    ∃ a z : integralSchemeNormalization X,
      integralSchemeNormalizationMap X a = x ∧ a ⤳ z ∧
        (integralSchemeNormalizationMap X ≫ j) z = y := by
  obtain ⟨a, ha⟩ := integralSchemeNormalizationMap_surjective X x
  let : IsIntegralHom (integralSchemeNormalizationMap X) :=
    integralSchemeNormalizationMap_isIntegralHom X
  have hclosed : IsClosedMap (integralSchemeNormalizationMap X ≫ j) :=
    j.isClosedEmbedding.isClosedMap.comp (integralSchemeNormalizationMap X).isClosedMap
  have hs : (integralSchemeNormalizationMap X ≫ j) a ⤳ y := by
    change j (integralSchemeNormalizationMap X a) ⤳ y
    rw [ha]
    exact hxy
  obtain ⟨z, hz, he⟩ := hclosed.specializingMap.closure_singleton_subset a hs.mem_closure
  exact ⟨a, z, ha, specializes_iff_mem_closure.mpr hz, he⟩

end DimensionFourDependence
