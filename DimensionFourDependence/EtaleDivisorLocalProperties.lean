import DimensionFourDependence.UnramifiedLocalOrder
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.EssentialFiniteness

/-! # All source-local properties of an étale divisor model

The local ring at a prime over the source DVR maximal ideal is itself
a DVR, torsion free, essentially of finite type, formally unramified,
and local over the source DVR. These properties are constructed together
for transport to the actual normalization local ring.
-/

namespace DimensionFourDependence

variable {O B : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing B] [IsDedekindDomain B] [Algebra O B] [Algebra.Etale O B]

/-- The given étale-model divisor supplies all properties needed for
normalized rational source-order equality after local identification. -/
theorem etale_divisor_local_source_properties (P : Ideal B) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal O)] :
    IsDiscreteValuationRing (Localization.AtPrime P) ∧
      Module.IsTorsionFree O (Localization.AtPrime P) ∧
      Algebra.EssFiniteType O (Localization.AtPrime P) ∧
      Algebra.FormallyUnramified O (Localization.AtPrime P) ∧
      IsLocalHom (algebraMap O (Localization.AtPrime P)) := by
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field O) P
  refine ⟨IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hPne _,
    inferInstance, inferInstance, inferInstance, ?_⟩
  have hm : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).under O =
      IsLocalRing.maximalIdeal O := by
    rw [← Ideal.under_under (B := B), Localization.AtPrime.under_maximalIdeal,
      ← Ideal.over_def P (IsLocalRing.maximalIdeal O)]
  exact ((IsLocalRing.local_hom_TFAE (algebraMap O (Localization.AtPrime P))).out 1 5).mpr hm

end DimensionFourDependence
