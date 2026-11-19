import DimensionFourDependence.UnramifiedDivisorOrder
import DimensionFourDependence.SourceDivisorMultiplicity
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # The actual source divisor DVR and the common-factor order bound

Localizing a Noetherian domain at a principal prime gives a DVR. Membership
in a power of its maximal ideal is exactly divisibility by that same prime
power in the original source ring. An unramified upstairs valuation thus
gives actual polynomial divisibility, and primitivity gives the degree
bound in Lemma 4.2. The geometric construction of this local extension
from a spread-out pencil curve is a separate step.
-/

namespace DimensionFourDependence

open IsLocalRing MvPolynomial

variable {R : Type*} [CommRing R] [IsDomain R]
  (P : Ideal R) [P.IsPrime] (δ : R) (hδ : Prime δ) (hP : P = Ideal.span {δ})

include hδ hP in
/-- The source localization at an actual irreducible divisor is a DVR. -/
theorem principal_prime_localization_isDVR [IsNoetherianRing R] :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  let A := Localization.AtPrime P
  let : IsNoetherianRing A := IsLocalization.isNoetherianRing P.primeCompl A inferInstance
  have hP0 : P ≠ ⊥ := by
    simpa only [hP, ne_eq, Ideal.span_singleton_eq_bot] using hδ.ne_zero
  have hnf : ¬ IsField A := IsLocalization.AtPrime.not_isField R hP0 A
  apply ((IsDiscreteValuationRing.TFAE A hnf).out 1 5).mpr
  have hm : maximalIdeal A = Ideal.span {algebraMap R A δ} := by
    calc
      maximalIdeal A = P.map (algebraMap R A) := (Localization.AtPrime.map_eq_maximalIdeal (I := P)).symm
      _ = (Ideal.span {δ}).map (algebraMap R A) := congrArg (Ideal.map (algebraMap R A)) hP
      _ = Ideal.span {algebraMap R A δ} := by rw [Ideal.map_span, Set.image_singleton]
  rw [hm]
  infer_instance

include hδ hP in
/-- An order bound in the actual source divisor local ring is equivalent
to prime-power divisibility in the original source ring. -/
theorem principal_prime_localization_power_mem_iff (x : R) (a : ℕ) :
    algebraMap R (Localization.AtPrime P) x ∈ maximalIdeal (Localization.AtPrime P) ^ a ↔ δ ^ a ∣ x := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := P), ← Ideal.map_pow,
    IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P)]
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hδs : ¬ δ ∣ s := by
      simpa only [Ideal.mem_primeCompl_iff, hP, Ideal.mem_span_singleton] using hs
    have hd : δ ^ a ∣ s * x := by
      rwa [hP, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hsx
    exact hδ.pow_dvd_of_dvd_mul_left a hδs hd
  · intro hd
    refine ⟨1, P.primeCompl.one_mem, ?_⟩
    rw [one_mul, hP, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hd

variable [IsNoetherianRing R]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra (Localization.AtPrime P) B]
  [Module.IsTorsionFree (Localization.AtPrime P) B] [Algebra.EssFiniteType (Localization.AtPrime P) B]
  (w : IsDedekindDomain.HeightOneSpectrum B)
  [w.asIdeal.LiesOver (maximalIdeal (Localization.AtPrime P))]
  [Algebra.IsUnramifiedAt (Localization.AtPrime P) w.asIdeal]

include hδ hP in
/-- A vanishing-order bound upstairs in an unramified extension of the
actual source divisor DVR descends to original-source prime divisibility. -/
theorem unramified_source_divisor_order_gives_power_divisibility (x : R) (a : ℕ)
    (horder : w.intValuation (algebraMap (Localization.AtPrime P) B
      (algebraMap R (Localization.AtPrime P) x)) ≤ WithZero.exp (-(a : ℤ))) : δ ^ a ∣ x := by
  let A := Localization.AtPrime P
  let : IsDiscreteValuationRing A := principal_prime_localization_isDVR P δ hδ hP
  let v : IsDedekindDomain.HeightOneSpectrum A :=
    ⟨maximalIdeal A, inferInstance, IsDiscreteValuationRing.not_a_field A⟩
  have hv : v.intValuation (algebraMap R A x) ≤ WithZero.exp (-(a : ℤ)) := by
    rw [unramified_divisor_intValuation v w]
    exact horder
  have hm := (v.intValuation_le_pow_iff_mem (algebraMap R A x) a).mp hv
  exact (principal_prime_localization_power_mem_iff P δ hδ hP x a).mp hm

variable {K : Type*} [Field K]

/-- The local algebraic conclusion of Lemma 4.2 in the original four
source variables: unramified upstairs orders on every original map
component force the asserted common-factor degree lower bound. -/
theorem unramified_source_orders_common_factor_degree
    (H V : Fin 4 → MvPolynomial (Fin 4) K) (g : MvPolynomial (Fin 4) K)
    (hg : g ≠ 0) (hV : IsPrimitiveVec V) (hHV : H = fun i => g * V i)
    (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime]
    (f : MvPolynomial (Fin 4) K) (hf : Irreducible f) (hQ : Q = Ideal.span {f})
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra (Localization.AtPrime Q) S]
    [Module.IsTorsionFree (Localization.AtPrime Q) S] [Algebra.EssFiniteType (Localization.AtPrime Q) S]
    (q : IsDedekindDomain.HeightOneSpectrum S)
    [q.asIdeal.LiesOver (maximalIdeal (Localization.AtPrime Q))]
    [Algebra.IsUnramifiedAt (Localization.AtPrime Q) q.asIdeal]
    (a : ℕ) (horder : ∀ i, q.intValuation (algebraMap (Localization.AtPrime Q) S
      (algebraMap (MvPolynomial (Fin 4) K) (Localization.AtPrime Q) (H i))) ≤ WithZero.exp (-(a : ℤ))) :
    f ^ a ∣ g ∧ a * f.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  apply source_divisor_multiplicity_common_factor_degree H V g hg hV hHV f hf a
  intro i
  exact unramified_source_divisor_order_gives_power_divisibility Q f (irreducible_iff_prime.mp hf)
    hQ q (H i) a (horder i)

end DimensionFourDependence
