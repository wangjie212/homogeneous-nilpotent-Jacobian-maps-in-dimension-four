import DimensionFourDependence.GenericFiberCoprimeBase
import DimensionFourDependence.GeometricParameterCrossRelation
import DimensionFourDependence.ParabolaPointNonvanishing

/-! # The original reduced parameter pencil is constant on geometric parabolas

The actual parameter cross relation and the rank-three base-locus
avoidance give nowhere vanishing numerator and denominator on the
entire geometric component. Its actual parabola coordinate algebra
then makes both original polynomial functions nonzero constants.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (s : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (s 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hrank : polyRank (jac H) = 3)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] [IsAlgClosed E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "G₀" => FractionRing (MvPolynomial (Fin 4) E ⧸ P)

include hY hh hrank hP

/-- The actual coprime parameter denominator is nowhere zero on
the entire original-coordinate zero locus of each geometric component. -/
theorem geometric_component_reduced_parameter_denominator_nowhere_zero
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p /
        algebraMap (MvPolynomial (Fin 4) K) S₀ q) :
    ∀ z : Fin 4 → E, (∀ R ∈ P, aeval z R = 0) → aeval z q ≠ 0 := by
  obtain ⟨tval, _htval, hcross⟩ :=
    geometric_component_closed_parameter_cross_relation H I s hY h hh e hrank E P hP p q hp hq ht
  intro z hz hzero
  have he := hz _ hcross
  have he' : aeval z p - tval * aeval z q = 0 := by
    simpa [aeval_def, MvPolynomial.eval₂_map] using he
  have hpzero : aeval z p = 0 := by simpa [hzero] using he'
  exact geometric_component_zero_locus_avoids_coprime_base H E P hP s hY p q hp hrel z hz
    ⟨hpzero, hzero⟩

/-- Both polynomials of the actual reduced closed Gauss pencil
are nonzero constants on every actual geometric parabolic component. -/
theorem geometric_parabola_reduced_parameter_pencil_nonzero_constants
    (hx : LiesInAffineParabola (L := E) (primeQuotientCoordinate P))
    (p q : MvPolynomial (Fin 4) K) (hp : p ≠ 0) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p /
        algebraMap (MvPolynomial (Fin 4) K) S₀ q) :
    ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧
      aeval (primeQuotientCoordinate P) (MvPolynomial.map (algebraMap K E) p) = algebraMap E G₀ a ∧
      aeval (primeQuotientCoordinate P) (MvPolynomial.map (algebraMap K E) q) = algebraMap E G₀ b := by
  have hnow := geometric_component_reduced_parameter_denominator_nowhere_zero
    H I s hY h hh e hrank E P hP p q hp hq hrel ht
  have hnow' : ∀ z : Fin 4 → E,
      (∀ R ∈ fiberVanishingIdeal (L := E) (primeQuotientCoordinate P), aeval z R = 0) →
        aeval z (MvPolynomial.map (algebraMap K E) q) ≠ 0 := by
    intro z hz
    have hz' : ∀ R ∈ P, aeval z R = 0 := by
      simpa only [primeQuotientCoordinate_relations] using hz
    simpa [aeval_def, MvPolynomial.eval₂_map] using hnow z hz'
  obtain ⟨b, hb, hbvalue⟩ := parabola_polynomial_nonvanishing_on_original_zero_locus_constant
    (primeQuotientCoordinate P) hx (MvPolynomial.map (algebraMap K E) q) hnow'
  obtain ⟨tval, htval, hcross⟩ :=
    geometric_component_closed_parameter_cross_relation H I s hY h hh e hrank E P hP p q hp hq ht
  have he : aeval (primeQuotientCoordinate P)
      (MvPolynomial.map (algebraMap K E) p - C tval * MvPolynomial.map (algebraMap K E) q) = 0 := by
    change _ ∈ fiberVanishingIdeal (L := E) (primeQuotientCoordinate P)
    exact (primeQuotientCoordinate_relations P).symm ▸ hcross
  simp only [map_sub, map_mul, aeval_C, hbvalue] at he
  exact ⟨tval * b, b, mul_ne_zero htval hb, hb,
    (sub_eq_zero.mp he).trans (map_mul (algebraMap E G₀) tval b).symm, hbvalue⟩

/-- The original homogeneous parameter construction supplies an
actual reduced pencil with the nonzero-constant conclusions. -/
theorem geometric_parabola_constructs_homogeneous_parameter_pencil_constants
    {d : ℕ} (hH : IsHomogMap H d)
    (hx : LiesInAffineParabola (L := E) (primeQuotientCoordinate P)) :
    ∃ p q : MvPolynomial (Fin 4) K, ∃ D : ℕ, 0 < D ∧ p ≠ 0 ∧ q ≠ 0 ∧
      p.IsHomogeneous D ∧ q.IsHomogeneous D ∧ IsRelPrime p q ∧
      closedGaussParameterSourceHom H I e RatFunc.X =
        algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q ∧
      ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧
        aeval (primeQuotientCoordinate P) (MvPolynomial.map (algebraMap K E) p) = algebraMap E G₀ a ∧
        aeval (primeQuotientCoordinate P) (MvPolynomial.map (algebraMap K E) q) = algebraMap E G₀ b := by
  obtain ⟨p, q, D, hD, hp, hq, hpH, hqH, hrel, ht⟩ :=
    actual_closed_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  exact ⟨p, q, D, hD, hp, hq, hpH, hqH, hrel, ht,
    geometric_parabola_reduced_parameter_pencil_nonzero_constants
      H I s hY h hh e hrank E P hP hx p q hp hq hrel ht⟩

end DimensionFourDependence
