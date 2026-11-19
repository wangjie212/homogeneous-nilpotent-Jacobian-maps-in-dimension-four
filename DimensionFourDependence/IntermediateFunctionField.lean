import DimensionFourDependence.Defs
import Mathlib.RingTheory.Localization.FractionRing

/-! # Function fields of intermediate coordinate rings

An injective intermediate algebra between a source domain and its
fraction field has that same fraction field. Every source rational
function is already a quotient of elements of the intermediate algebra.
-/

namespace DimensionFourDependence

variable {R S F : Type*} [CommRing R] [CommRing S] [Field F]
  [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F]
  [IsFractionRing R F] [FaithfulSMul S F]

include R in
/-- Adjoining compatible coefficients or functions inside the original
source fraction field does not change the actual function field. -/
theorem intermediate_algebra_same_fraction_field : IsFractionRing S F := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨r, s, hs, hrep⟩ := IsFractionRing.div_surjective R z
  refine ⟨algebraMap R S r, algebraMap R S s, ?_⟩
  simpa only [← IsScalarTower.algebraMap_apply R S F] using hrep.symm

end DimensionFourDependence
