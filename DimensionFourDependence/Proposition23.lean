import DimensionFourDependence.HomogeneousDependenceTheorem
import DimensionFourDependence.GeometricPlanarFiber

/-! # Proposition 2.3 over the original characteristic-zero field -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 2450000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "F" => FractionRing R₄

/-- The right-kernel direction criterion of Proposition 2.3. The chosen
nonzero projective coordinate represents the function field of the actual
direction image. The stronger dependence theorem proves this case over
the original field as well. -/
theorem proposition_2_3_direction_curve
    (H : Fin 4 → R₄) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (_hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (_hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (_hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P))
    (u : Fin 4 → F) (a : Fin 4) (_ha : u a ≠ 0)
    (_hker : (jac H).map (algebraMap R₄ F) *ᵥ u = 0)
    (_hDim : Algebra.trdeg K (projectiveRatioField (K := K) u a) ≤ 1) : ComponentsDependent H :=
  theorem_1_1 d hd H hH hN

/-- The two alternatives in Proposition 2.3, expressed for a minimal
prime of the generic fiber over the full output field. The fixed-plane
case uses the geometric comparison in the proof of the proposition. -/
theorem proposition_2_3
    (H : Fin 4 → R₄) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (E : Type u) [Field E] [IsAlgClosed E] [Algebra (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E]
    [Algebra K E] [IsScalarTower K (polynomialOutputField H) E]
    (P : Ideal (MvPolynomial (Fin 4) E)) [P.IsPrime]
    (hP : P ∈ (extendCoefficientIdeal E (fiberVanishingIdeal
      (L := polynomialOutputField H) (rationalCoordinate (K := K) (n := 4)))).minimalPrimes)
    (hline : ¬ LiesInAffineLine (E := E) (primeQuotientCoordinate P))
    (h : (∃ (u : Fin 4 → F) (a : Fin 4), u a ≠ 0 ∧
        (jac H).map (algebraMap R₄ F) *ᵥ u = 0 ∧ Algebra.trdeg K (projectiveRatioField (K := K) u a) ≤ 1) ∨
      ∃ v w : Fin 4 → K, LinearIndependent K ![v, w] ∧
        LiesInConstantPlaneTranslate (E := E) v w (primeQuotientCoordinate P)) : ComponentsDependent H := by
  rcases h with ⟨u, a, ha, hk, hdim⟩ | ⟨v, w, hvw, hplane⟩
  · exact proposition_2_3_direction_curve H hd hH hN hrank E P hP hline u a ha hk hdim
  · exact dependence_of_geometric_nonlinear_fixed_plane_fiber H hd hH hN hrank E P hP v w hvw hplane hline

end DimensionFourDependence
