import DimensionFourDependence.NormalCodimensionOneRegularity
import Mathlib.RingTheory.DedekindDomain.Dvr

/-! # A height-one pole of a level reciprocal is a level divisor

The canonical localization of a normal Noetherian domain at a height-one
prime is a discrete valuation ring. A pole of `(f-c)⁻¹` therefore makes
`f-c` regular and vanishing there, so `f` has residue `c` at that actual
prime. These are original-field values, not a valuation extension.
-/

namespace DimensionFourDependence

variable (R : Type*) {F : Type*} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- The actual height-one prime localization inside the specified
fraction field is a discrete valuation ring. -/
theorem normal_height_one_prime_local_algebra_isDVR
    (P : Ideal R) [P.IsPrime] (hheight : P.height = 1) :
    IsDiscreteValuationRing (fractionPrimeLocalAlgebra (F := F) R P) := by
  let T := fractionPrimeLocalAlgebra (F := F) R P
  let : IsLocalization.AtPrime T P :=
    Localization.subalgebra.isLocalization_ofField F P.primeCompl P.primeCompl_le_nonZeroDivisors
  let : IsLocalRing T := IsLocalization.AtPrime.isLocalRing T P
  let : IsNoetherianRing T := IsLocalization.isNoetherianRing P.primeCompl T inferInstance
  let : IsIntegrallyClosed T :=
    isIntegrallyClosed_of_isLocalization T P.primeCompl P.primeCompl_le_nonZeroDivisors
  have hht : (IsLocalRing.maximalIdeal T).height = 1 := by
    rw [← IsLocalization.height_under P.primeCompl (IsLocalRing.maximalIdeal T),
      IsLocalization.AtPrime.under_maximalIdeal T P, hheight]
  have hdim : ringKrullDim T = 1 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hht]
    rfl
  let : Ring.KrullDimLE 1 T := Ring.krullDimLE_iff.mpr hdim.le
  have htfae : ValuationRing T ↔ IsIntegrallyClosed T ∧
      ∀ Q : Ideal T, Q ≠ ⊥ → Q.IsPrime → Q = IsLocalRing.maximalIdeal T :=
    (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain T).out 2 4
  have hval : ValuationRing T := htfae.mpr
    ⟨inferInstance, fun Q hQ hprime =>
      IsLocalRing.eq_maximalIdeal (hprime.isMaximal_of_ne_bot hQ)⟩
  have hnf : ¬IsField T := IsLocalization.AtPrime.not_isField R
    (Ideal.ne_bot_of_height_eq_one hheight) T
  exact ((IsDiscreteValuationRing.TFAE T hnf).out 1 2).mpr hval

/-- A height-one pole of the translated reciprocal puts the actual
level difference in the maximal ideal of the same localization. -/
theorem height_one_reciprocal_pole_is_level
    (P : Ideal R) [P.IsPrime] (hheight : P.height = 1) (f c : F)
    (hpole : (f - c)⁻¹ ∉ fractionPrimeLocalAlgebra R P) :
    ∃ z : fractionPrimeLocalAlgebra R P, (z : F) = f - c ∧
      letI : IsLocalRing (fractionPrimeLocalAlgebra (F := F) R P) :=
        IsLocalization.AtPrime.isLocalRing _ P
      z ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) R P) := by
  let T := fractionPrimeLocalAlgebra (F := F) R P
  let : IsDiscreteValuationRing T := normal_height_one_prime_local_algebra_isDVR R P hheight
  obtain hreg | ⟨z, hz⟩ := ValuationRing.isInteger_or_isInteger T ((f - c)⁻¹)
  · obtain ⟨u, hu⟩ := hreg
    exact (hpole (hu ▸ u.property)).elim
  have hz' : (z : F) = f - c := by
    change (z : F) = ((f - c)⁻¹)⁻¹ at hz
    simpa only [inv_inv] using hz
  refine ⟨z, hz', ?_⟩
  rw [IsLocalRing.mem_maximalIdeal]
  intro hu
  apply hpole
  have he : (↑(hu.unit⁻¹) : F) = (f - c)⁻¹ := by
    have he := map_units_inv (algebraMap T F) hu.unit
    change ((↑(hu.unit⁻¹) : T) : F) = ((hu.unit : T) : F)⁻¹ at he
    simpa only [hu.unit_spec, hz'] using he
  exact he ▸ (↑(hu.unit⁻¹) : T).property

/-- A nonregular level reciprocal supplies a height-one prime and
an actual local-ring element vanishing there with value `f-c`. -/
theorem normal_nonregular_reciprocal_constructs_height_one_level
    (f c : F) (hreg : ¬IsLocalization.IsInteger R ((f - c)⁻¹)) :
    ∃ (P : Ideal R) (_hP : P.IsPrime), P.height = 1 ∧
      ∃ z : fractionPrimeLocalAlgebra R P, (z : F) = f - c ∧
        letI : IsLocalRing (fractionPrimeLocalAlgebra (F := F) R P) :=
          IsLocalization.AtPrime.isLocalRing _ P
        z ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) R P) := by
  obtain ⟨P, hP, hh, hpole⟩ :=
    normal_nonregular_fraction_constructs_height_one_pole R ((f - c)⁻¹) hreg
  exact ⟨P, hP, hh, height_one_reciprocal_pole_is_level R P hh f c hpole⟩

end DimensionFourDependence
