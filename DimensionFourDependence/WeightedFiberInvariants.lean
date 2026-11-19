import DimensionFourDependence.HomogeneousFiberWeights

/-! # Constructing the weighted invariant data used in Section 3.2

The original homogeneous nilpotent rank-three polynomial map supplies
all coefficients, their defining equations and the three Euler weights.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The actual coefficients of (2.2) have the Euler weights used in
Proposition 3.1. No weight, chart or invariant is an additional hypothesis. -/
theorem exists_weighted_fiber_invariants_polynomial
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) :
    let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
      fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => Q (p i.castSucc)))
      (h c q k : coefficientField (K := K) (fun i : Fin 3 => Q (p i.castSucc))),
      (h : FractionRing (MvPolynomial (Fin 4) K)) = Q (p 3) ∧
      (c : FractionRing (MvPolynomial (Fin 4) K)) =
        firstFiberInvariantInChart p (fun i : Fin 3 => Q (p i.castSucc)) hY h ∧
      (q : FractionRing (MvPolynomial (Fin 4) K)) =
        secondFiberInvariant p (fun i : Fin 3 => Q (p i.castSucc)) hY h c ∧
      (k : FractionRing (MvPolynomial (Fin 4) K)) =
        thirdFiberInvariant p (fun i : Fin 3 => Q (p i.castSucc)) hY h c q ∧
      coefficientEuler _ hY h = h ∧
      coefficientEuler _ hY c = algebraMap K _ ((d : K)⁻¹) * c ∧
      coefficientEuler _ hY q = algebraMap K _ (2 * (d : K)⁻¹ - 1) * q := by
  obtain ⟨p, hY, h, c, q, k, hh, hc, hq, hk⟩ := exists_three_fiber_invariants_polynomial H hN hrank
  exact ⟨p, hY, h, c, q, k, hh, hc, hq, hk,
    homogeneous_last_output_euler H hd hH p hY h hh,
    firstFiberInvariant_output_weight H hd hH p hY h c hh hc,
    secondFiberInvariant_output_weight H hd hH p hY h c q hh hc hq⟩

end DimensionFourDependence
