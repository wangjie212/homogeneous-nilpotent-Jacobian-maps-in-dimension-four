import DimensionFourDependence.ThirdCovector

/-! # The cubic fiber invariant in Lemma 2.2

This completes the construction of all three field-theoretic invariants
in (2.2). The geometric complete-intersection and degree assertions are
separate obligations.
-/

namespace DimensionFourDependence

open Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The expression `k = (∇q)ᵀx - (1/2)D²c[x,x] - (1/6)D³h[x,x,x]`. -/
noncomputable def thirdFiberInvariant (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c q : coefficientField (K := K) Y) : FractionRing (MvPolynomial (Fin 4) K) :=
  cubicExpression
    (fun i => (coefficientPartial (K := K) Y hY i q : FractionRing (MvPolynomial (Fin 4) K)))
    (fiberHessian Y hY c) (fiberThirdDerivative Y hY h)
    (fun i => rationalCoordinate (K := K) (p i.castSucc))

/-- The vertical derivative of the cubic expression is its fixed-
coefficient gradient `a` paired with the tangent direction. -/
theorem thirdFiberInvariant_deriv
    (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c q : coefficientField (K := K) Y)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hker : rationalJacobian Y *ᵥ u = 0) :
    sourceVectorDerivation u (thirdFiberInvariant p Y hY h c q) =
      ∑ i : Fin 3, fiberThirdCovector p Y hY h c q i * u (p i.castSucc) := by
  have hd := cubicExpression_deriv (sourceVectorDerivation u)
    (fun i => (coefficientPartial (K := K) Y hY i q : FractionRing (MvPolynomial (Fin 4) K)))
    (fiberHessian Y hY c) (fiberThirdDerivative Y hY h)
    (fun i => rationalCoordinate (K := K) (p i.castSucc))
    (fun i => tangent_derivation_kills_coefficients Y u hker (coefficientPartial (K := K) Y hY i q))
    (fun i j => tangent_derivation_kills_coefficients Y u hker
      (coefficientPartial (K := K) Y hY i (coefficientPartial (K := K) Y hY j c)))
    (fun i j k => tangent_derivation_kills_coefficients Y u hker
      (coefficientPartial (K := K) Y hY i (coefficientPartial (K := K) Y hY j
        (coefficientPartial (K := K) Y hY k h))))
    (fiberHessian_symmetric Y hY c) (fiberThirdDerivative_swap12 Y hY h)
    (fiberThirdDerivative_swap23 Y hY h)
  simpa only [thirdFiberInvariant, fiberThirdCovector, sourceVectorDerivation_coordinate] using hd

/-- The cubic expression belongs to the coefficient field under the
original nilpotent rank-three hypotheses and the preceding invariant equations. -/
theorem thirdFiberInvariant_mem_of_nilpotent_rank_three
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (h c q : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3))
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) =
      firstFiberInvariantInChart p (fun i : Fin 3 => H (p i.castSucc)) hY h)
    (hq : (q : FractionRing (MvPolynomial (Fin 4) K)) =
      secondFiberInvariant p (fun i : Fin 3 => H (p i.castSucc)) hY h c) :
    thirdFiberInvariant p (fun i : Fin 3 => H (p i.castSucc)) hY h c q ∈
      coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)) := by
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i => H (p i.castSucc)
  obtain ⟨u, hu0, hu⟩ := matrix_nilpotent_exists_nonzero_kernel _ hN (by omega)
  have hker : rationalJacobian Y *ᵥ u = 0 := by
    funext i
    exact congrFun hu (p i.castSucc)
  let a := fiberThirdCovector p Y hY h c q
  let b := fiberSecondCovector p Y hY h c
  obtain ⟨ha, hb, hν, _⟩ := fiber_covector_chain H p hY h c q hh hc hq
  have hdot := nilpotent_third_covector_kernel_dot_zero _ hN hrank
    (Fin.snoc a 0 ∘ p.symm) (Fin.snoc b 0 ∘ p.symm) (fiberNormal Y hY h ∘ p.symm) u ha hb hν hu
  rw [comp_equiv_symm_dotProduct] at hdot
  have hz : (∑ i : Fin 3, a i * u (p i.castSucc)) = 0 := by
    simpa [dotProduct, Fin.sum_univ_castSucc, Fin.snoc] using hdot
  change thirdFiberInvariant p Y hY h c q ∈ (coefficientField (K := K) Y).restrictScalars K
  rw [← tangent_derivation_constants Y hY u hu0 hker]
  change sourceVectorDerivation u (thirdFiberInvariant p Y hY h c q) = 0
  rw [thirdFiberInvariant_deriv p Y hY h c q u hker]
  exact hz

/-- Construct all three expressions of (2.2) as elements of the actual
coefficient field of a nilpotent rank-three rational map. -/
theorem exists_three_fiber_invariants
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3) :
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
      (h c q k : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))),
      (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3) ∧
        (c : FractionRing (MvPolynomial (Fin 4) K)) =
          firstFiberInvariantInChart p (fun i : Fin 3 => H (p i.castSucc)) hY h ∧
        (q : FractionRing (MvPolynomial (Fin 4) K)) =
          secondFiberInvariant p (fun i : Fin 3 => H (p i.castSucc)) hY h c ∧
        (k : FractionRing (MvPolynomial (Fin 4) K)) =
          thirdFiberInvariant p (fun i : Fin 3 => H (p i.castSucc)) hY h c q := by
  obtain ⟨p, hY, h, c, q, hh, hc, hq⟩ := exists_first_two_fiber_invariants H hN hrank
  have hk := thirdFiberInvariant_mem_of_nilpotent_rank_three H hN hrank p hY h c q hh hc hq
  let k : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)) :=
    ⟨thirdFiberInvariant p (fun i : Fin 3 => H (p i.castSucc)) hY h c q, hk⟩
  exact ⟨p, hY, h, c, q, k, hh, hc, hq, rfl⟩

/-- The three invariant equations under the polynomial Jacobian and
rational-rank conventions of the paper, with all intermediate choices derived. -/
theorem exists_three_fiber_invariants_polynomial
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) :
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
          thirdFiberInvariant p (fun i : Fin 3 => Q (p i.castSucc)) hY h c q := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hJ : rationalJacobian Q = (jac H).map
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))) :=
    rationalJacobian_polynomial H
  apply exists_three_fiber_invariants Q
  · rw [hJ]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))).mapMatrix
  · rw [hJ]
    exact hrank

end DimensionFourDependence
