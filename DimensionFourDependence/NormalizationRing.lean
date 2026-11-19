import DimensionFourDependence.FiniteNormalization

/-! # The finite normal birational ring and extension of rational roots

This is the integral closure in the actual fraction field. It is normal,
has the same fraction field, and is finite for finite-type domains in
characteristic zero. A rational function whose positive power is regular
belongs to this normalization; this is the local extension argument used
for rational sections in Section 4.2.
-/

namespace DimensionFourDependence

variable (A : Type*) [CommRing A] [IsDomain A]

/-- The normalization ring in the canonical fraction field. -/
noncomputable def normalizationRing := integralClosure A (FractionRing A)

/-- The normalization has the same actual fraction field. -/
theorem normalizationRing_isFractionRing : IsFractionRing (normalizationRing A) (FractionRing A) := by
  let : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  exact integralClosure.isFractionRing_of_algebraic
    (fun x hx => (IsFractionRing.injective A (FractionRing A)) (hx.trans (map_zero _).symm))

/-- The normalization ring is integrally closed. -/
theorem normalizationRing_isIntegrallyClosed : IsIntegrallyClosed (normalizationRing A) := by
  exact integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing A)

omit [IsDomain A] in
/-- A positive-power regular rational function extends to the normalization. -/
theorem rational_root_mem_normalization (x : FractionRing A) {d : ℕ} (hd : 0 < d)
    (a : A) (hx : x ^ d = algebraMap A (FractionRing A) a) :
    x ∈ normalizationRing A := by
  apply IsIntegral.of_pow hd
  rw [hx]
  exact isIntegral_algebraMap

variable {K : Type*} [Field K] [CharZero K] [Algebra K A] [Algebra.FiniteType K A]

include K in
/-- The actual normal birational ring is finite over the original domain. -/
theorem normalizationRing_finite : Module.Finite A (normalizationRing A) :=
  finite_normalization_of_finiteType (K := K)

include K in
/-- The finite normalization of an affine characteristic-zero variety
is Noetherian. -/
theorem normalizationRing_isNoetherianRing : IsNoetherianRing (normalizationRing A) := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let : Module.Finite A (normalizationRing A) := normalizationRing_finite A (K := K)
  exact IsNoetherianRing.of_finite A (normalizationRing A)

end DimensionFourDependence
