import DimensionFourDependence.ValuationLocalOverring
import DimensionFourDependence.PrimeLocalizationFunctionField

/-! # A local overring of a Dedekind domain is its contracted localization

The actual inclusion into a common fraction field fixes the local
isomorphism and all original ring values. No target-DVR property or
independently chosen local comparison is assumed.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {S B : Type*} [CommRing S] [IsDedekindDomain S]
  [CommRing B] [IsLocalRing B] [Algebra S B]

/-- The actual overring inclusion extends to the localization at its
contracted maximal ideal, preserving every original ring element. -/
noncomputable def dedekindOverringLocalHom
    (q : Ideal S) [q.IsPrime] (hq : q = (IsLocalRing.maximalIdeal B).under S) :
    Localization.AtPrime q →ₐ[S] B :=
  IsLocalization.liftAlgHom (M := q.primeCompl) (f := Algebra.ofId S B) fun s => by
    apply IsLocalRing.notMem_maximalIdeal.mp
    change algebraMap S B (s : S) ∉ IsLocalRing.maximalIdeal B
    simpa only [hq, Ideal.mem_primeCompl_iff, Ideal.mem_under] using s.property

/-- This induced actual map is a local homomorphism. -/
theorem dedekindOverringLocalHom_isLocalHom
    (q : Ideal S) [q.IsPrime] (hq : q = (IsLocalRing.maximalIdeal B).under S) :
    IsLocalHom (dedekindOverringLocalHom q hq).toRingHom := by
  apply IsLocalHom.mk
  intro z hz
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl z
  apply (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime q) q r s).mpr
  have hs : IsUnit (algebraMap S B (s : S)) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    simpa only [hq, Ideal.mem_primeCompl_iff, Ideal.mem_under] using s.property
  have hspec := congrArg (dedekindOverringLocalHom q hq)
    (IsLocalization.mk'_spec (Localization.AtPrime q) r s)
  simp only [map_mul, AlgHom.commutes] at hspec
  have hr : IsUnit (algebraMap S B r) := hspec ▸ hz.mul hs
  have hr' : algebraMap S B r ∉ IsLocalRing.maximalIdeal B :=
    IsLocalRing.notMem_maximalIdeal.mpr hr
  simpa only [hq, Ideal.mem_primeCompl_iff, Ideal.mem_under] using hr'

/-- The local overring is exactly the contracted-prime localization,
through its actual original-ring inclusion in the common fraction field. -/
noncomputable def dedekindLocalOverringEquiv
    (L : Type*) [Field L] [Algebra S L] [Algebra B L]
    [IsScalarTower S B L] [IsFractionRing S L] [FaithfulSMul B L]
    (q : Ideal S) [q.IsPrime] (hq : q = (IsLocalRing.maximalIdeal B).under S)
    (hq0 : q ≠ ⊥) : Localization.AtPrime q ≃ₐ[S] B := by
  let k := dedekindOverringLocalHom q hq
  let : IsDiscreteValuationRing (Localization.AtPrime q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq0 _
  let : Algebra (Localization.AtPrime q) B := k.toRingHom.toAlgebra
  let : IsScalarTower S (Localization.AtPrime q) B :=
    IsScalarTower.of_algebraMap_eq (fun s => (k.commutes s).symm)
  let : Algebra (Localization.AtPrime q) L := primeLocalizationFractionAlgebra q
  let : IsScalarTower S (Localization.AtPrime q) L := primeLocalizationFraction_scalarTower q
  let : IsFractionRing (Localization.AtPrime q) L := primeLocalizationFraction_isFractionRing q
  let : IsLocalHom (algebraMap (Localization.AtPrime q) B) :=
    dedekindOverringLocalHom_isLocalHom q hq
  let : IsScalarTower (Localization.AtPrime q) B L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext q.primeCompl
    ext s
    change algebraMap (Localization.AtPrime q) L (algebraMap S (Localization.AtPrime q) s) =
      algebraMap B L (k (algebraMap S (Localization.AtPrime q) s))
    rw [← IsScalarTower.algebraMap_apply S (Localization.AtPrime q) L,
      k.commutes, ← IsScalarTower.algebraMap_apply S B L]
  exact AlgEquiv.ofBijective k
    (valuation_local_overring_algebraMap_bijective
      (A := Localization.AtPrime q) (B := B) (F := L))

end DimensionFourDependence
