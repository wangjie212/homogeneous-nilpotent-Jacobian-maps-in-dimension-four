import DimensionFourDependence.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Recovering source local rings from intermediate coordinate algebras

An injectively embedded algebra between a source ring and its divisor
localization has the same local ring at the contracted maximal ideal.
This criterion identifies local rings without presuming an isomorphism
between the global coordinate algebras.
-/

namespace DimensionFourDependence

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  [IsLocalRing A] [FaithfulSMul S A]

/-- Every injective intermediate source algebra localizes to the same
source divisor local ring at the contracted maximal ideal. -/
theorem intermediate_algebra_source_localization
    (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime A P] :
    IsLocalization.AtPrime A ((IsLocalRing.maximalIdeal A).under S) := by
  let Q := (IsLocalRing.maximalIdeal A).under S
  change IsLocalization Q.primeCompl A
  refine ⟨?_, ?_, ?_⟩
  · intro s
    apply IsLocalRing.notMem_maximalIdeal.mp
    exact s.property
  · intro a
    obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj P.primeCompl a
    have hden : algebraMap R S (s : R) ∈ Q.primeCompl := by
      change algebraMap S A (algebraMap R S (s : R)) ∉ IsLocalRing.maximalIdeal A
      rw [← IsScalarTower.algebraMap_apply R S A]
      simpa using IsLocalization.map_units A s
    refine ⟨(algebraMap R S r, ⟨algebraMap R S s, hden⟩), ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply R S A] using hs
  · intro x y hxy
    exact ⟨1, by simpa using FaithfulSMul.algebraMap_injective S A hxy⟩

/-- The induced isomorphism identifies the intermediate algebra's
prime localization with the original source local ring. -/
noncomputable def intermediateSourceLocalEquiv
    (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime A P] :
    Localization.AtPrime ((IsLocalRing.maximalIdeal A).under S) ≃ₐ[S] A := by
  let : IsLocalization.AtPrime A ((IsLocalRing.maximalIdeal A).under S) :=
    intermediate_algebra_source_localization P
  exact IsLocalization.algEquiv ((IsLocalRing.maximalIdeal A).under S).primeCompl _ _

end DimensionFourDependence
