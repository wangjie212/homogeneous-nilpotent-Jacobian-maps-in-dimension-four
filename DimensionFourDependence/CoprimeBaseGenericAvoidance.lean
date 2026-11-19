import DimensionFourDependence.TranscendenceDegreeSpecialization
import Mathlib.RingTheory.Ideal.UFD

/-! # A coprime base locus cannot carry three independent outputs

In a factorial affine domain of dimension four, two relatively prime
nonzero equations cut a locus of dimension at most two. The proof uses
strict transcendence-degree drops of actual prime quotients. In
particular, a point of affine four-space where three polynomial outputs
remain independent cannot be a common zero of a coprime pair.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] [UniqueFactorizationMonoid A]

/-- A prime containing a relatively prime pair in a four-dimensional
factorial affine domain has residue transcendence degree less than three. -/
theorem relPrime_pair_prime_quotient_trdeg_lt_three
    (hA : Algebra.trdeg K A = 4) (P : Ideal A) [P.IsPrime]
    (p q : A) (hp0 : p ≠ 0) (hrel : IsRelPrime p q) (hp : p ∈ P) (hq : q ∈ P) :
    Algebra.trdeg K (A ⧸ P) < 3 := by
  classical
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  by_contra hn
  have hge : 3 ≤ Algebra.trdeg K (A ⧸ P) := le_of_not_gt hn
  have hPne : P ≠ ⊥ := by
    intro he
    exact hp0 (Ideal.mem_bot.mp (he ▸ hp))
  obtain ⟨δ, hδP, hδprime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot
    (inferInstance : P.IsPrime) hPne
  let Q : Ideal A := Ideal.span {δ}
  let : Q.IsPrime := Ideal.isPrime_span_singleton_of_prime hδprime
  have hQP : Q ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hδP)
  have hQne : Q ≠ ⊥ := by
    intro he
    apply hδprime.ne_zero
    exact Ideal.mem_bot.mp (he ▸ (Ideal.subset_span (Set.mem_singleton δ)))
  have hlt : Algebra.trdeg K (A ⧸ Q) < 4 :=
    (prime_quotient_trdeg_lt (K' := K) Q hQne
      (trdeg_lt_aleph0_of_finiteType (R := K) (S := A))).trans_eq hA
  have hle : Algebra.trdeg K (A ⧸ Q) ≤ 3 :=
    (Cardinal.lt_natCast_add_one_iff (n := 3)).mp (by convert hlt using 1; norm_num)
  let g := Ideal.Quotient.factorₐ K hQP
  have hgs : Function.Surjective g := Ideal.Quotient.factor_surjective hQP
  have hPQ : Algebra.trdeg K (A ⧸ P) ≤ Algebra.trdeg K (A ⧸ Q) :=
    trdeg_le_of_surjective g hgs
  have heq : Algebra.trdeg K (A ⧸ Q) = Algebra.trdeg K (A ⧸ P) :=
    le_antisymm (hle.trans hge) hPQ
  have hginj := surjective_algHom_injective_of_trdeg_eq g hgs
    (trdeg_lt_aleph0_of_finiteType (R := K) (S := A ⧸ Q)) heq
  have hPQ' : P ≤ Q := by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hginj
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr ha).trans (map_zero g).symm
  have hδp : δ ∣ p := Ideal.mem_span_singleton.mp (hPQ' hp)
  have hδq : δ ∣ q := Ideal.mem_span_singleton.mp (hPQ' hq)
  exact hδprime.not_isUnit (hrel hδp hδq)

variable {E : Type*} [Field E] [Algebra K E]

/-- Three independent polynomial values at an actual extension-field
point exclude every original relatively prime base pair at that point. -/
theorem three_independent_polynomial_values_avoid_coprime_base
    (z : Fin 4 → E) (H : Fin 3 → MvPolynomial (Fin 4) K)
    (hH : AlgebraicIndependent K (fun i => aeval z (H i)))
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hrel : IsRelPrime p q) :
    ¬ (aeval z p = 0 ∧ aeval z q = 0) := by
  rintro ⟨hp, hq⟩
  let I := RingHom.ker (aeval z : MvPolynomial (Fin 4) K →ₐ[K] E)
  let : I.IsPrime := RingHom.ker_isPrime _
  let f : (MvPolynomial (Fin 4) K ⧸ I) →ₐ[K] E :=
    Ideal.kerLiftAlg (aeval z : MvPolynomial (Fin 4) K →ₐ[K] E)
  let w : Fin 3 → (MvPolynomial (Fin 4) K ⧸ I) := fun i => Ideal.Quotient.mk I (H i)
  have hind : AlgebraicIndependent K w := by
    apply AlgebraicIndependent.of_comp f
    have he : f ∘ w = fun i => aeval z (H i) := by
      funext i
      exact Ideal.kerLiftAlg_mk (aeval z : MvPolynomial (Fin 4) K →ₐ[K] E) (H i)
    rwa [he]
  have hge : 3 ≤ Algebra.trdeg K (MvPolynomial (Fin 4) K ⧸ I) := by
    simpa using hind.lift_cardinalMk_le_trdeg
  have hlt := relPrime_pair_prime_quotient_trdeg_lt_three
    (K := K) (A := MvPolynomial (Fin 4) K) (by simp) I p q hp0 hrel hp hq
  exact not_le_of_gt hlt hge

end DimensionFourDependence
