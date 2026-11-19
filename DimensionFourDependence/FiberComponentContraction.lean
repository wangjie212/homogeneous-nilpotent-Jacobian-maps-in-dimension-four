import DimensionFourDependence.FiberAlgebraicBaseChange

/-! # Components of a scalar-extended fiber contract to the original prime

Flatness gives going down. A minimal prime over the extended fiber ideal
therefore contracts to the original fiber prime, with no extra relations.
-/

namespace DimensionFourDependence

/-- Under going down, a minimal prime over an extended prime contracts to that prime. -/
theorem minimalPrime_under_eq_of_hasGoingDown {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S] (P : Ideal R) [P.IsPrime]
    (Q : Ideal S) (hQ : Q ∈ (P.map (algebraMap R S)).minimalPrimes) : Q.under R = P := by
  have : Q.IsPrime := hQ.isPrime
  have hle : P ≤ Q.under R := Ideal.map_le_iff_le_comap.mp hQ.le
  obtain ⟨J, hJQ, hJ, hJP⟩ := Q.exists_ideal_le_liesOver_of_le (p := P) (q := Q.under R) hle
  have : J.IsPrime := hJ
  have : J.LiesOver P := hJP
  have hmap : P.map (algebraMap R S) ≤ J :=
    Ideal.map_le_iff_le_comap.mpr (J.over_def P).le
  have he : Q = J := le_antisymm (hQ.2 ⟨hJ, hmap⟩ hJQ) hJQ
  rw [he]
  exact (J.over_def P).symm

open MvPolynomial

variable {L : Type*} [Field L] (E : Type*) [Field E] [Algebra L E] {σ : Type*}

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Coefficient-field extension makes the extended polynomial ring a flat module. -/
theorem coefficientPolynomialExtension_flat :
    Module.Flat (MvPolynomial σ L) (MvPolynomial σ E) := by
  exact Module.Flat.of_linearEquiv
    (Algebra.IsPushout.equiv L (MvPolynomial σ L) E (MvPolynomial σ E)).symm.toLinearEquiv

/-- Every component prime after field extension has exactly the original prime as contraction. -/
theorem minimalPrime_extended_coefficients_comap (P : Ideal (MvPolynomial σ L)) [P.IsPrime]
    (Q : Ideal (MvPolynomial σ E)) (hQ : Q ∈ (extendCoefficientIdeal E P).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap L E)) = P := by
  have : Module.Flat (MvPolynomial σ L) (MvPolynomial σ E) := coefficientPolynomialExtension_flat E
  exact minimalPrime_under_eq_of_hasGoingDown P Q hQ

end DimensionFourDependence
