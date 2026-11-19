import DimensionFourDependence.ZeroPoleLevelClosure
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-! # General rational levels avoid fixed boundary divisors

A rational function has at most one constant residue at a given prime.
Only finitely many height-one primes contain a prescribed nonzero
denominator. Consequently, outside a finite set of constants, every
height-one level prime avoids that denominator. This connects the
maximal regular domain to the original quotient's domain.
-/

namespace DimensionFourDependence

variable {k R F : Type*} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- At a fixed prime, a rational function has at most one level
value from the original coefficient field. -/
theorem rationalLevelLocus_constant_unique
    (f : F) (p : PrimeSpectrum R) (c d : k)
    (hc : p ∈ rationalLevelLocus R f (algebraMap k R c))
    (hd : p ∈ rationalLevelLocus R f (algebraMap k R d)) : c = d := by
  obtain ⟨a, s, hs, ha, hac⟩ := hc
  obtain ⟨b, t, ht, hb, hbd⟩ := hd
  have he : t * a = s * b := by
    apply IsFractionRing.injective R F
    rw [map_mul, map_mul, ← ha, ← hb]
    ring
  have hdelta : (algebraMap k R c - algebraMap k R d) * (s * t) ∈ p.asIdeal := by
    convert p.asIdeal.sub_mem (p.asIdeal.mul_mem_left s hbd)
      (p.asIdeal.mul_mem_left t hac) using 1
    linear_combination he
  have hst : s * t ∉ p.asIdeal :=
    fun h => (p.isPrime.mem_or_mem h).elim hs ht
  have hdiff : algebraMap k R (c - d) ∈ p.asIdeal := by
    rw [map_sub]
    exact (p.isPrime.mem_or_mem hdelta).resolve_right hst
  by_contra hcd
  have hu : IsUnit (algebraMap k R (c - d)) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hcd)).map (algebraMap k R)
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hdiff hu)

/-- Any original quotient equation gives its original numerator
level equation at every point in the rational level locus. -/
theorem rationalLevelLocus_original_quotient_equation
    (f : F) (a b c : R) (hf : algebraMap R F b * f = algebraMap R F a)
    (p : PrimeSpectrum R) (hp : p ∈ rationalLevelLocus R f c) :
    a - c * b ∈ p.asIdeal := by
  obtain ⟨n, s, hs, hn, hnc⟩ := hp
  have he : s * a = b * n := by
    apply IsFractionRing.injective R F
    rw [map_mul, map_mul, ← hf, ← hn]
    ring
  have hprod : s * (a - c * b) ∈ p.asIdeal := by
    convert p.asIdeal.mul_mem_left b hnc using 1
    linear_combination he
  exact (p.isPrime.mem_or_mem hprod).resolve_left hs

variable [IsNoetherianRing R]

/-- Only finitely many coefficient-field constants can have a
height-one level prime contained in a fixed denominator's zero set. -/
theorem finite_exceptional_levels_for_denominator
    (f : F) (b : R) (hb : b ≠ 0) :
    ∃ S : Set k, S.Finite ∧ ∀ c ∉ S, ∀ p : PrimeSpectrum R,
      p.asIdeal.height = 1 → p ∈ rationalLevelLocus R f (algebraMap k R c) → b ∉ p.asIdeal := by
  let D : Set (PrimeSpectrum R) :=
    {p | p.asIdeal ∈ (Ideal.span {b}).minimalPrimes}
  have hinj : Function.Injective (fun p : PrimeSpectrum R => p.asIdeal) :=
    fun p q h => PrimeSpectrum.ext h
  have hD : D.Finite := Set.Finite.preimage hinj.injOn
    (Ideal.span {b}).finite_minimalPrimes_of_isNoetherianRing
  let S : Set k := ⋃ p ∈ D, {c | p ∈ rationalLevelLocus R f (algebraMap k R c)}
  have hS : S.Finite := hD.biUnion fun p hp =>
    (show Set.Subsingleton {c | p ∈ rationalLevelLocus R f (algebraMap k R c)} from
      fun c hc d hd => rationalLevelLocus_constant_unique f p c d hc hd).finite
  refine ⟨S, hS, ?_⟩
  intro c hc p hh hp hbp
  have hpD : p ∈ D := by
    apply Ideal.mem_minimalPrimes_of_height_le
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbp))
    rw [hh]
    exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hb)
  apply hc
  exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpD, hp⟩⟩

end DimensionFourDependence
