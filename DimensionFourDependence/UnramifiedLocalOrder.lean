import DimensionFourDependence.UnramifiedDivisorOrder
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Orders in the unramified divisor local ring

The global normalized divisor valuation comparison is equivalent to
membership in powers of the actual upstairs local maximal ideal. This
is the form that transports through the normalization local isomorphism.
-/

namespace DimensionFourDependence

variable {O B : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing B] [IsDedekindDomain B] [Algebra O B]
  [Module.IsTorsionFree O B] [Algebra.EssFiniteType O B]
  (P : Ideal B) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal O)]
  [Algebra.IsUnramifiedAt O P]

/-- Every regular source function has exactly the same maximal-ideal
power bounds in an unramified source-divisor local extension. -/
theorem unramified_divisor_local_maximalIdeal_pow_mem_iff (x : O) (a : ℕ) :
    algebraMap O (Localization.AtPrime P) x ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ a ↔
    x ∈ (IsLocalRing.maximalIdeal O) ^ a := by
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field O) P
  let : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hPne
  let v : IsDedekindDomain.HeightOneSpectrum O :=
    ⟨IsLocalRing.maximalIdeal O, inferInstance, IsDiscreteValuationRing.not_a_field O⟩
  let w : IsDedekindDomain.HeightOneSpectrum B := ⟨P, inferInstance, hPne⟩
  rw [IsScalarTower.algebraMap_apply O B (Localization.AtPrime P)]
  change algebraMap O B x ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime P)) ^ a).under B ↔ _
  rw [IsLocalization.AtPrime.under_maximalIdeal_pow P (Localization.AtPrime P) a]
  rw [← w.intValuation_le_pow_iff_mem, ← v.intValuation_le_pow_iff_mem,
    unramified_divisor_intValuation v w]

end DimensionFourDependence
