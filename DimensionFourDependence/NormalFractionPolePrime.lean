import DimensionFourDependence.FractionDenominatorIdeal
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Height-one poles in a normal Noetherian domain

A prime denominator ideal of a nonregular fraction is minimal over a
nonzero principal ideal. The essential normality argument is the finite
module integrality criterion: a nonregular fraction cannot preserve its
own nonzero denominator ideal. This supplies the height-one prime needed
to detect poles, rather than assuming a codimension-one regularity rule.
-/

namespace DimensionFourDependence

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- A prime denominator ideal of a nonregular fraction in a normal
Noetherian domain is a height-one prime. -/
theorem prime_fraction_denominator_height_one
    (x : F) (hx : ¬IsLocalization.IsInteger R x)
    (P : Ideal R) [P.IsPrime] (hP : P = fractionDenominatorIdeal R x) :
    P.height = 1 := by
  have hP0 : P ≠ ⊥ := hP ▸ fractionDenominatorIdeal_ne_bot R x
  let M : Submodule R F := Submodule.map (Algebra.linearMap R F) P
  have hM0 : M ≠ ⊥ := by
    intro he
    apply hP0
    apply le_antisymm ?_ bot_le
    intro a ha
    change a = 0
    have hmem : algebraMap R F a ∈ M := ⟨a, ha, rfl⟩
    rw [he, Submodule.mem_bot] at hmem
    apply IsFractionRing.injective R F
    simpa only [map_zero] using hmem
  have hnotstable : ¬∀ z ∈ M, x * z ∈ M := by
    intro hstable
    have hint : IsIntegral R x := isIntegral_of_smul_mem_submodule M hM0
      (Submodule.FG.map _ (IsNoetherian.noetherian P)) x hstable
    exact hx (IsIntegrallyClosed.algebraMap_eq_of_integral hint)
  push Not at hnotstable
  obtain ⟨z, ⟨a, ha, rfl⟩, hza⟩ := hnotstable
  obtain ⟨b, hb⟩ := (mem_fractionDenominatorIdeal R x a).mp (hP ▸ ha)
  have hbP : b ∉ P := by
    intro h
    apply hza
    refine ⟨b, h, ?_⟩
    change algebraMap R F b = x * algebraMap R F a
    simpa only [mul_comm] using hb
  have hmin : P ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨inferInstance, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)⟩, ?_⟩
    intro Q hQ hQP
    intro r hr
    have haQ : a ∈ Q := hQ.2 (Ideal.subset_span rfl)
    obtain ⟨c, hc⟩ := (mem_fractionDenominatorIdeal R x r).mp (hP ▸ hr)
    have he : r * b = a * c := by
      apply IsFractionRing.injective R F
      rw [map_mul, map_mul, hb, hc]
      ring
    have hrb : r * b ∈ Q := he ▸ Q.mul_mem_right c haQ
    exact (hQ.1.mem_or_mem hrb).resolve_right (fun h => hbP (hQP h))
  apply le_antisymm
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin
  · exact Order.one_le_iff_ne_zero.mpr
      ((Ideal.height_eq_zero_iff_eq_bot (I := P)).not.mpr hP0)

/-- Every nonregular fraction in the specified function field has
a height-one prime containing all of its denominator multipliers. -/
theorem normal_nonregular_fraction_constructs_height_one_prime
    (x : F) (hx : ¬IsLocalization.IsInteger R x) :
    ∃ P : Ideal R, P.IsPrime ∧ P.height = 1 ∧ fractionDenominatorIdeal R x ≤ P := by
  obtain ⟨y, P, hprime, hy, hP, hle⟩ :=
    nonregular_fraction_constructs_prime_denominator R x hx
  let : P.IsPrime := hprime
  exact ⟨P, hprime, prime_fraction_denominator_height_one y hy P hP, hle⟩

end DimensionFourDependence
