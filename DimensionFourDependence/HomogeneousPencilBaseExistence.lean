import DimensionFourDependence.VertexLinePrimeIdentification
import DimensionFourDependence.ClosedGaussHomogeneousParameter

/-! # Positive homogeneous pencils have actual height-two base components -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

/-- A positive-degree homogeneous equation vanishes at the affine origin. -/
theorem positive_homogeneous_polynomial_aeval_origin
    (p : MvPolynomial (Fin 4) K) {D : ℕ} (hD : 0 < D) (hp : p.IsHomogeneous D) :
    aeval (0 : Fin 4 → K) p = 0 := by
  have hc : p.coeff 0 = 0 := hp.coeff_eq_zero (by simpa using hD.ne)
  rw [aeval_zero]
  change p.coeff 0 = 0
  exact hc

/-- The positive homogeneous base ideal is proper, by its actual
origin evaluation, rather than a supplied nonemptiness hypothesis. -/
theorem positive_homogeneous_pair_span_ne_top
    (p q : MvPolynomial (Fin 4) K) {D : ℕ} (hD : 0 < D)
    (hp : p.IsHomogeneous D) (hq : q.IsHomogeneous D) :
    Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≠ ⊤ := by
  let J : Ideal (MvPolynomial (Fin 4) K) :=
    RingHom.ker (aeval (0 : Fin 4 → K)).toRingHom
  have hJ : J.IsPrime := RingHom.ker_isPrime _
  have hle : Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) ≤ J := by
    apply Ideal.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with hz | hz
    · rw [hz]
      exact positive_homogeneous_polynomial_aeval_origin p hD hp
    · rw [Set.mem_singleton_iff.mp hz]
      exact positive_homogeneous_polynomial_aeval_origin q hD hq
  intro he
  exact hJ.ne_top (top_le_iff.mp (he ▸ hle))

/-- Coprime positive homogeneous equations construct a minimal base
prime of height exactly two and a transverse generic coordinate. -/
theorem positive_homogeneous_coprime_pair_constructs_base_component
    (p q : MvPolynomial (Fin 4) K) {D : ℕ} (hD : 0 < D)
    (hp0 : p ≠ 0) (hp : p.IsHomogeneous D) (hq : q.IsHomogeneous D)
    (hrel : IsRelPrime p q) :
    ∃ Q : Ideal (MvPolynomial (Fin 4) K),
      Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes ∧
      Q.height = 2 ∧ ∃ i : Fin 3, X i.castSucc ∉ Q := by
  obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_minimalPrimes
    (positive_homogeneous_pair_span_ne_top p q hD hp hq)
  let : Q.IsPrime := hQ.1.1
  have hle := two_equation_base_minimal_prime_height_le_two p q Q hQ
  have hge := two_le_prime_height_of_relPrime_mem Q p q hp0
    (hQ.1.2 (Ideal.subset_span (by simp)))
    (hQ.1.2 (Ideal.subset_span (by simp))) hrel
  exact ⟨Q, hQ, le_antisymm hle hge,
    height_le_two_prime_has_transverse_coordinate Q hle⟩

variable [CharZero K]

/-- The original closed Gauss parameter constructs its positive
homogeneous reduced pencil together with a genuine height-two base component. -/
theorem actual_closed_gauss_parameter_constructs_nonempty_base_component
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) :
    ∃ (p q : MvPolynomial (Fin 4) K) (D : ℕ)
      (Q : Ideal (MvPolynomial (Fin 4) K)),
      0 < D ∧ p ≠ 0 ∧ q ≠ 0 ∧ p.IsHomogeneous D ∧ q.IsHomogeneous D ∧
      IsRelPrime p q ∧
      closedGaussParameterSourceHom H I e RatFunc.X =
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
          algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q ∧
      Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes ∧
      Q.height = 2 ∧ ∃ i : Fin 3, X i.castSucc ∉ Q := by
  obtain ⟨p, q, D, hD, hp0, hq0, hp, hq, hrel, hparameter⟩ :=
    actual_closed_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  obtain ⟨Q, hQ, hh, hoff⟩ :=
    positive_homogeneous_coprime_pair_constructs_base_component p q hD hp0 hp hq hrel
  exact ⟨p, q, D, Q, hD, hp0, hq0, hp, hq, hrel, hparameter, hQ, hh, hoff⟩

end DimensionFourDependence
