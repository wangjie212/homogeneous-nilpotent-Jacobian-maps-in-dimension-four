import DimensionFourDependence.FixedVertexNumeratorBaseZero
import DimensionFourDependence.NormalCodimensionOneRegularity

/-! # The actual pencil-base numerator constructs a vanishing branch germ

At a prime above the pencil base where the tangent-plane section is a
unit, the actual numerator's radical base relation constructs a regular
vanishing germ of n(H)/L^d. No vanishing germ or valuation residue is
assumed. Existence and incidence of the required branch prime are
separate geometric steps.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {A F : Type*} [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F]

/-- A numerator in a prime and a denominator avoiding it construct
the actual regular vanishing fraction germ at that same prime. -/
theorem quotient_constructs_vanishing_prime_local_germ
    (Q : Ideal A) [Q.IsPrime] (n l : A) (hn : n ∈ Q) (hl : l ∉ Q) (d : ℕ) :
    ∃ z : fractionPrimeLocalAlgebra (F := F) A Q,
      (z : F) = algebraMap A F n / (algebraMap A F l) ^ d ∧
      z ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) A Q) := by
  let T := fractionPrimeLocalAlgebra (F := F) A Q
  let s : Q.primeCompl := ⟨l, hl⟩
  let z : T := IsLocalization.mk' T n (s ^ d)
  have hl0 : algebraMap A F l ≠ 0 := by
    apply (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr
    intro he
    exact hl (he ▸ Q.zero_mem)
  refine ⟨z, ?_, ?_⟩
  · apply (eq_div_iff (pow_ne_zero d hl0)).mpr
    have he := congrArg (fun t : T => (t : F)) (IsLocalization.mk'_spec T n (s ^ d))
    change (z : F) * algebraMap A F (l ^ d) = algebraMap A F n at he
    simpa only [map_pow] using he
  · exact (IsLocalization.AtPrime.mk'_mem_maximal_iff T Q n (s ^ d)).mpr hn

variable {S : Type*} [CommRing S]

/-- A radical base relation supplies the numerator's vanishing in
every prime above that base, and hence the actual quotient zero germ
where the denominator is a unit. -/
theorem radical_base_relation_constructs_quotient_zero_germ
    (J : Ideal S) (N L : S) (hN : N ∈ J.radical) (φ : S →+* A)
    (Q : Ideal A) [Q.IsPrime] (hJ : J ≤ Q.comap φ) (hL : φ L ∉ Q) (d : ℕ) :
    ∃ z : fractionPrimeLocalAlgebra (F := F) A Q,
      (z : F) = algebraMap A F (φ N) / (algebraMap A F (φ L)) ^ d ∧
      z ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) A Q) := by
  have hNQ : φ N ∈ Q :=
    ((Ideal.IsPrime.radical_le_iff (inferInstance : (Q.comap φ).IsPrime)).mpr hJ) hN
  exact quotient_constructs_vanishing_prime_local_germ Q (φ N) (φ L) hNQ hL d

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]

/-- At any branch prime above the original pencil base where the
tangent-plane section is nonzero, the original actual second-normal
numerator constructs its own vanishing local quotient germ. -/
theorem actual_gauss_root_numerator_constructs_base_branch_zero_germ
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q)
    (n : Fin 4 → E) (hn : HasActualGaussRootNumerator H I E e n)
    (L : MvPolynomial (Fin 4) E) (φ : MvPolynomial (Fin 4) E →+* A)
    (Q : Ideal A) [Q.IsPrime]
    (hpQ : φ (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) p) ∈ Q)
    (hqQ : φ (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) q) ∈ Q)
    (hL : φ L ∉ Q) :
    ∃ z : fractionPrimeLocalAlgebra (F := F) A Q,
      (z : F) = algebraMap A F (φ (extendedClosedGaussOutputLinearPolynomial H I E n)) /
        (algebraMap A F (φ L)) ^ d ∧
      z ∈ IsLocalRing.maximalIdeal (fractionPrimeLocalAlgebra (F := F) A Q) := by
  have hNbase := actual_gauss_root_numerator_mem_extended_pencil_base_radical
    H I E hd hH hind hGauss hvertex e p q hq hrel hparameter n hn
  apply radical_base_relation_constructs_quotient_zero_germ
    _ (extendedClosedGaussOutputLinearPolynomial H I E n) L hNbase φ Q ?_ hL d
  apply Ideal.span_le.mpr
  intro P hP
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with rfl | rfl
  · exact hpQ
  · exact hqQ

end DimensionFourDependence
