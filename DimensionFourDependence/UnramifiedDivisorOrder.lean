import DimensionFourDependence.Defs
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-! # Unramified local extensions preserve divisor orders

The normalized adic valuations agree at primes lying over one another
when the extension is unramified. This includes all rational functions,
and equivalent prime-power conditions on regular functions. These are the
local order statements needed after the geometric spreading step in
Lemma 4.2; no spreading hypothesis is silently presumed here.
-/

namespace DimensionFourDependence

variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.IsTorsionFree A B]
  [Algebra.EssFiniteType A B]
  (v : IsDedekindDomain.HeightOneSpectrum A) (w : IsDedekindDomain.HeightOneSpectrum B)
  [w.asIdeal.LiesOver v.asIdeal] [Algebra.IsUnramifiedAt A w.asIdeal]

/-- Unramifiedness makes the actual divisor ramification index one. -/
theorem unramified_divisor_ramification_index_one :
    v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

/-- The normalized divisor valuations of a regular source function agree. -/
theorem unramified_divisor_intValuation (x : A) :
    v.intValuation x = w.intValuation (algebraMap A B x) := by
  have h := v.intValuation_liesOver w x
  rw [unramified_divisor_ramification_index_one v w, pow_one] at h
  exact h

/-- Every lower bound on vanishing order of a regular function is the
same upstairs and downstairs in an unramified local extension. -/
theorem unramified_divisor_prime_power_iff (x : A) (a : ℕ) :
    w.asIdeal ^ a ∣ Ideal.span {algebraMap A B x} ↔ v.asIdeal ^ a ∣ Ideal.span {x} := by
  rw [← w.intValuation_le_pow_iff_dvd, ← v.intValuation_le_pow_iff_dvd,
    ← unramified_divisor_intValuation v w x]

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]

/-- The normalized divisor valuations agree for every rational function,
so the order comparison applies to locally trivialized rational sections. -/
theorem unramified_divisor_rational_valuation (x : K) :
    v.valuation K x = w.valuation L (algebraMap K L x) := by
  have h := v.valuation_liesOver L w x
  rw [unramified_divisor_ramification_index_one v w, pow_one] at h
  exact h

end DimensionFourDependence
