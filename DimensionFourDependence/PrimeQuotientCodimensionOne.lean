import DimensionFourDependence.NormalizationResidueDimensionExact
import Mathlib.RingTheory.Ideal.UFD

/-! # A two-dimensional prime image in an affine threefold is a divisor -/

namespace DimensionFourDependence

universe u

variable {k A : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A] [UniqueFactorizationMonoid A]

/-- In a three-dimensional finite-type factorial domain, a prime
quotient of dimension two has height one. The principal prime below it
is constructed, and any strictly larger prime would force a second
strict transcendence-degree drop. -/
theorem prime_height_eq_one_of_quotient_trdeg_two
    (hA : Algebra.trdeg k A = 3) (P : Ideal A) [P.IsPrime]
    (hP : Algebra.trdeg k (A ⧸ P) = 2) : P.height = 1 := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hPne : P ≠ ⊥ := by
    intro he
    have hinj : Function.Injective (Ideal.Quotient.mkₐ k P) := by
      apply (injective_iff_map_eq_zero _).mpr
      intro a ha
      have hm : a ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp ha
      rwa [he, Ideal.mem_bot] at hm
    have hle := trdeg_le_of_injective (Ideal.Quotient.mkₐ k P) hinj
    rw [hA, hP] at hle
    norm_num at hle
  obtain ⟨δ, hδP, hδprime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot
    (inferInstance : P.IsPrime) hPne
  let Q : Ideal A := Ideal.span {δ}
  let : Q.IsPrime := Ideal.isPrime_span_singleton_of_prime hδprime
  have hQP : Q ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hδP)
  have hQheight : Q.height = 1 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hδprime.ne_zero) hδprime.not_isUnit
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hQheight
  have hQlt : Algebra.trdeg k (A ⧸ Q) < 3 :=
    (prime_quotient_trdeg_lt (K' := k) Q hQne
      (trdeg_lt_aleph0_of_finiteType (R := k) (S := A))).trans_eq hA
  have hQle : Algebra.trdeg k (A ⧸ Q) ≤ 2 :=
    (Cardinal.lt_natCast_add_one_iff (n := 2)).mp (by convert hQlt using 1; norm_num)
  let g := Ideal.Quotient.factorₐ k hQP
  have hgs : Function.Surjective g := Ideal.Quotient.factor_surjective hQP
  have hge : 2 ≤ Algebra.trdeg k (A ⧸ Q) := hP.symm.trans_le (trdeg_le_of_surjective g hgs)
  have hdim : Algebra.trdeg k (A ⧸ Q) = Algebra.trdeg k (A ⧸ P) :=
    (le_antisymm hQle hge).trans hP.symm
  have hginj := surjective_algHom_injective_of_trdeg_eq g hgs
    (trdeg_lt_aleph0_of_finiteType (R := k) (S := A ⧸ Q)) hdim
  have heq : P = Q := by
    apply le_antisymm _ hQP
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hginj
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr ha).trans (map_zero g).symm
  exact (congrArg Ideal.height heq).trans hQheight

/-- The same criterion can be stated using the actual quotient
fraction field, the form supplied by residue-field comparisons. -/
theorem prime_height_eq_one_of_fraction_trdeg_two
    (hA : Algebra.trdeg k A = 3) (P : Ideal A) [P.IsPrime]
    (hP : Algebra.trdeg k (FractionRing (A ⧸ P)) = 2) : P.height = 1 :=
  prime_height_eq_one_of_quotient_trdeg_two hA P
    ((fractionRing_trdeg_eq_base (k := k) (A := A ⧸ P)).symm.trans hP)

end DimensionFourDependence
