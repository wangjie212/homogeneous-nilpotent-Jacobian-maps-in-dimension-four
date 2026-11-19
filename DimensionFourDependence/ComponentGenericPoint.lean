import DimensionFourDependence.FiberComponentContraction

/-! # Generic points of component primes and transcendental coordinates -/

namespace DimensionFourDependence

open MvPolynomial

variable {E : Type*} [Field E] {n : ℕ}

/-- The generic affine coordinates in the fraction field of a prime quotient. -/
noncomputable def primeQuotientCoordinate (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime] :
    Fin n → FractionRing (MvPolynomial (Fin n) E ⧸ P) :=
  fun i => algebraMap (MvPolynomial (Fin n) E ⧸ P) _ (Ideal.Quotient.mk P (X i))

theorem primeQuotientCoordinate_aeval (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime]
    (p : MvPolynomial (Fin n) E) :
    aeval (primeQuotientCoordinate P) p =
      algebraMap (MvPolynomial (Fin n) E ⧸ P) (FractionRing (MvPolynomial (Fin n) E ⧸ P))
        (Ideal.Quotient.mk P p) := by
  let f := (IsScalarTower.toAlgHom E (MvPolynomial (Fin n) E ⧸ P)
      (FractionRing (MvPolynomial (Fin n) E ⧸ P))).comp (Ideal.Quotient.mkₐ E P)
  have he : aeval (primeQuotientCoordinate P) = f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [f, primeQuotientCoordinate]
  exact DFunLike.congr_fun he p

/-- The generic point has exactly the prescribed prime as its relation ideal. -/
theorem primeQuotientCoordinate_relations (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime] :
    fiberVanishingIdeal (L := E) (primeQuotientCoordinate P) = P := by
  ext p
  change aeval (primeQuotientCoordinate P) p = 0 ↔ p ∈ P
  rw [primeQuotientCoordinate_aeval]
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (MvPolynomial (Fin n) E ⧸ P) (FractionRing (MvPolynomial (Fin n) E ⧸ P))
    simpa only [map_zero] using h
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

variable {L F G : Type*} [Field L] [Field F] [Field G] [Algebra L F] [Algebra L G]

/-- Equality of relation ideals preserves transcendence of individual coordinates. -/
theorem transcendental_coordinate_of_relations_eq (x : Fin n → F) (z : Fin n → G)
    (hrel : fiberVanishingIdeal (L := L) z = fiberVanishingIdeal (L := L) x)
    (i : Fin n) (hi : Transcendental L (x i)) : Transcendental L (z i) := by
  intro hz
  obtain ⟨p, hp, hpz⟩ := hz
  let q := Polynomial.aeval (X i : MvPolynomial (Fin n) L) p
  have hzq : q ∈ fiberVanishingIdeal (L := L) z := by
    change aeval z q = 0
    have he := Polynomial.aeval_algHom_apply (aeval z : MvPolynomial (Fin n) L →ₐ[L] G) (X i) p
    simp only [aeval_X] at he
    exact he.symm.trans hpz
  rw [hrel] at hzq
  have hxq : Polynomial.aeval (x i) p = 0 := by
    have he := Polynomial.aeval_algHom_apply (aeval x : MvPolynomial (Fin n) L →ₐ[L] F) (X i) p
    simpa only [aeval_X] using he.trans hzq
  exact hi ⟨p, hp, hxq⟩

variable [Algebra L E]

/-- The prime-quotient generic point contracts to the original fiber relations. -/
theorem componentGenericPoint_original_relations (x : Fin n → F)
    (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal (L := L) x)).minimalPrimes) :
    fiberVanishingIdeal (L := L) (primeQuotientCoordinate P) = fiberVanishingIdeal (L := L) x := by
  rw [← fiberVanishingIdeal_comap_coefficients (L := L) (E := E), primeQuotientCoordinate_relations]
  exact minimalPrime_extended_coefficients_comap E _ P hP

/-- In an algebraic coefficient extension, a transcendental coordinate
remains transcendental on every component of the extended fiber. -/
theorem componentGenericPoint_transcendental [Algebra.IsAlgebraic L E] (x : Fin n → F)
    (P : Ideal (MvPolynomial (Fin n) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal (L := L) x)).minimalPrimes)
    (i : Fin n) (hi : Transcendental L (x i)) : Transcendental E (primeQuotientCoordinate P i) := by
  have hz := transcendental_coordinate_of_relations_eq x (primeQuotientCoordinate P)
    (componentGenericPoint_original_relations x P hP) i hi
  exact hz.extendScalars E

end DimensionFourDependence
