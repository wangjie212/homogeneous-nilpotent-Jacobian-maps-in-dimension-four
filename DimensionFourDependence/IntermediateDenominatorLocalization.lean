import DimensionFourDependence.Defs
import Mathlib.RingTheory.Localization.Basic

/-! # Keeping source denominators through intermediate coordinate algebras

An injective intermediate algebra between a source ring and its given
denominator localization has that same localization after inverting the
images of the original source denominators. No locality is required.
-/

namespace DimensionFourDependence

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [FaithfulSMul S A]

/-- The original source denominators still give the same ring after
passing through an injective intermediate coordinate algebra. -/
theorem intermediate_algebra_denominator_localization
    (M : Submonoid R) [IsLocalization M A] :
    IsLocalization (Algebra.algebraMapSubmonoid S M) A := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    obtain ⟨r, hr, he⟩ := s.property
    change IsUnit (algebraMap S A s.val)
    rw [← he, ← IsScalarTower.algebraMap_apply R S A]
    exact IsLocalization.map_units A ⟨r, hr⟩
  · intro a
    obtain ⟨⟨r, m⟩, hm⟩ := IsLocalization.surj M a
    refine ⟨(algebraMap R S r, ⟨algebraMap R S m,
      Algebra.mem_algebraMapSubmonoid_of_mem _⟩), ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply R S A] using hm
  · intro s s' hss'
    exact ⟨1, by simpa using FaithfulSMul.algebraMap_injective S A hss'⟩

end DimensionFourDependence
