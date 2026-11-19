import DimensionFourDependence.FiniteFlatDvrMultiplicity
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! # Multiplicity on a finite function-field normalization

For every finite extension of a characteristic-zero DVR fraction field,
the actual normalization is finite and flat of rank equal to that field
degree. Source uniformizer orders at all its primes are bounded by it.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [CharZero K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Module.Finite K L]

/-- At every actual normalization prime above a source DVR divisor,
the uniformizer's local order is bounded by the actual extension degree. -/
theorem dvr_normalization_uniformizer_order_le_field_degree
    (q : Ideal (integralClosure A L)) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal A)]
    (π : A) (hπ : Irreducible π) (a : ℕ)
    (horder : algebraMap A (Localization.AtPrime q) π ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a) :
    a ≤ Module.finrank K L := by
  let S := integralClosure A L
  let : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr (by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K))
  let : Module.Finite A S := IsIntegralClosure.finite A K L S
  let : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain A K L S
  let : Module.Free A S := IsIntegralClosure.module_free A K L S
  let : Module.Flat A S := inferInstance
  let : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr (by
    intro x y hxy
    apply FaithfulSMul.algebraMap_injective A L
    exact congrArg Subtype.val hxy)
  have h := finite_flat_dedekind_uniformizer_order_le_rank (A := A) (S := S) q π hπ a horder
  rw [IsIntegralClosure.rank A K L S] at h
  exact h

end DimensionFourDependence
