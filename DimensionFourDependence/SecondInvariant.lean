import DimensionFourDependence.FirstInvariantChart
import DimensionFourDependence.NilpotentFlag
import DimensionFourDependence.QuadraticDifferentiation

/-! # The quadratic fiber invariant in Lemma 2.2 -/

namespace DimensionFourDependence

open Matrix

/-- Collect the coefficient derivatives of an affine fiber equation. -/
theorem collect_affine_coefficient_derivatives {F : Type*} [Field F] {n : ℕ}
    (a dy x : Fin n → F) (T : Matrix (Fin n) (Fin n) F) :
    (∑ i, a i * dy i) + (∑ j, (∑ i, T i j * dy i) * x j) =
      ∑ i, (a i + ∑ j, T i j * x j) * dy i := by
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {K : Type*} [Field K] [CharZero K]

/-- The Hessian with respect to the independent output coordinates. -/
noncomputable def fiberHessian
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) :
    Matrix (Fin 3) (Fin 3) (FractionRing (MvPolynomial (Fin 4) K)) :=
  Matrix.of fun i j => (coefficientPartial (K := K) Y hY i
    (coefficientPartial (K := K) Y hY j h) : FractionRing (MvPolynomial (Fin 4) K))

/-- The covector `b = ∇c + (D²h)x` in the proof of Lemma 2.2. -/
noncomputable def fiberSecondCovector
    (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y) : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) :=
  fun i => (coefficientPartial (K := K) Y hY i c : FractionRing (MvPolynomial (Fin 4) K)) +
    ∑ j, fiberHessian Y hY h i j * rationalCoordinate (K := K) (p j.castSucc)

/-- The expression `q = (∇c)ᵀx + (1/2)D²h[x,x]` in (2.2). -/
noncomputable def secondFiberInvariant
    (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y) : FractionRing (MvPolynomial (Fin 4) K) :=
  quadraticExpression
    (fun i => (coefficientPartial (K := K) Y hY i c : FractionRing (MvPolynomial (Fin 4) K)))
    (fiberHessian Y hY h) (fun i => rationalCoordinate (K := K) (p i.castSucc))

/-- Mixed coefficient derivatives make the Hessian symmetric. -/
theorem fiberHessian_symmetric
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (i j : Fin 3) :
    fiberHessian Y hY h i j = fiberHessian Y hY h j i :=
  congrArg (fun a : coefficientField (K := K) Y => (a : FractionRing (MvPolynomial (Fin 4) K)))
    (coefficientPartials_commute Y hY i j h)

/-- Differentiating the first invariant produces the covector identity
`bᵀ B = (-∇hᵀ,1)`, with the actual algebraic coefficient derivatives. -/
theorem fiberSecondCovector_jacobian
    (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y)
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p Y hY h) :
    fiberSecondCovector p Y hY h c ᵥ* rationalJacobian Y = fiberNormal Y hY h ∘ p.symm := by
  funext j
  let D := rationalPartial (K := K) j
  have heq : (c : FractionRing (MvPolynomial (Fin 4) K)) =
      rationalCoordinate (K := K) (p 3) - ∑ i : Fin 3,
        fiberGradient Y hY h i * rationalCoordinate (K := K) (p i.castSucc) := hc
  have hd := linear_fiber_equation_derivative D
    (fun i : Fin 3 => rationalCoordinate (K := K) (p i.castSucc)) (fiberGradient Y hY h)
    (rationalCoordinate (K := K) (p 3)) (c : FractionRing (MvPolynomial (Fin 4) K)) heq
  have hdc : D (c : FractionRing (MvPolynomial (Fin 4) K)) =
      ∑ i : Fin 3, (coefficientPartial (K := K) Y hY i c : FractionRing (MvPolynomial (Fin 4) K)) *
        D (Y i) := by
    rw [coefficient_chain_rule Y hY]
    simp only [mul_comm]
  have hdg (k : Fin 3) : D (fiberGradient Y hY h k) =
      ∑ i : Fin 3, fiberHessian Y hY h i k * D (Y i) := by
    rw [show fiberGradient Y hY h k =
      (coefficientPartial (K := K) Y hY k h : FractionRing (MvPolynomial (Fin 4) K)) from rfl,
      coefficient_chain_rule Y hY]
    simp only [fiberHessian, Matrix.of_apply, mul_comm]
  rw [hdc] at hd
  simp only [hdg] at hd
  rw [collect_affine_coefficient_derivatives] at hd
  have hnormal (k : Fin 4) : rationalPartial (K := K) (p k) (rationalCoordinate (K := K) (p 3)) -
      ∑ i : Fin 3, fiberGradient Y hY h i *
        rationalPartial (K := K) (p k) (rationalCoordinate (K := K) (p i.castSucc)) =
          fiberNormal Y hY h k := by
    fin_cases k <;>
      simp [rationalPartial_coordinate, p.injective.eq_iff, fiberNormal, Fin.snoc, Fin.sum_univ_succ]
    congr 1
  have hn : D (rationalCoordinate (K := K) (p 3)) -
      ∑ i : Fin 3, fiberGradient Y hY h i * D (rationalCoordinate (K := K) (p i.castSucc)) =
        (fiberNormal Y hY h ∘ p.symm) j := by
    simpa only [D, p.apply_symm_apply, Function.comp_apply] using hnormal (p.symm j)
  rw [hn] at hd
  exact hd.symm

/-- The quadratic equation has a nonzero gradient at the generic point. -/
theorem fiberSecondCovector_ne_zero (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y)
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p Y hY h) :
    fiberSecondCovector p Y hY h c ≠ 0 := by
  intro hb
  have hz := fiberSecondCovector_jacobian p Y hY h c hc
  rw [hb, zero_vecMul] at hz
  have hi := congrFun hz (p (Fin.last 3))
  simp [fiberNormal, Fin.snoc] at hi

/-- A vertical derivative of the quadratic expression is its fixed-
coefficient gradient `b` paired with the first three tangent components. -/
theorem secondFiberInvariant_deriv
    (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hker : rationalJacobian Y *ᵥ u = 0) :
    sourceVectorDerivation u (secondFiberInvariant p Y hY h c) =
      ∑ i : Fin 3, fiberSecondCovector p Y hY h c i * u (p i.castSucc) := by
  have hd := quadraticExpression_deriv (sourceVectorDerivation u)
    (fun i => (coefficientPartial (K := K) Y hY i c : FractionRing (MvPolynomial (Fin 4) K)))
    (fiberHessian Y hY h) (fun i => rationalCoordinate (K := K) (p i.castSucc))
    (fun i => tangent_derivation_kills_coefficients Y u hker (coefficientPartial (K := K) Y hY i c))
    (fun i j => tangent_derivation_kills_coefficients Y u hker
      (coefficientPartial (K := K) Y hY i (coefficientPartial (K := K) Y hY j h)))
    (fiberHessian_symmetric Y hY h)
  simpa only [secondFiberInvariant, fiberSecondCovector, sourceVectorDerivation_coordinate] using hd

/-- The quadratic expression belongs to the coefficient field under the
nilpotent rank-three Jacobian hypotheses and the already established first
invariant equation. -/
theorem secondFiberInvariant_mem_of_nilpotent_rank_three
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (h c : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3))
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) =
      firstFiberInvariantInChart p (fun i : Fin 3 => H (p i.castSucc)) hY h) :
    secondFiberInvariant p (fun i : Fin 3 => H (p i.castSucc)) hY h c ∈
      coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)) := by
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i => H (p i.castSucc)
  obtain ⟨u, hu0, hu⟩ := matrix_nilpotent_exists_nonzero_kernel _ hN (by omega)
  have hker : rationalJacobian Y *ᵥ u = 0 := by
    funext i
    exact congrFun hu (p i.castSucc)
  have hchart : Fin.snoc Y (h : FractionRing (MvPolynomial (Fin 4) K)) = H ∘ p := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
      change (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3)
      exact hh
    · simp only [Fin.snoc_castSucc, Y, Function.comp_apply]
  let b := fiberSecondCovector p Y hY h c
  have hframe : Fin.snoc b 0 ᵥ* fiberFrame Y hY h = b := by
    funext i
    simp [vecMul, dotProduct, Fin.sum_univ_castSucc, fiberFrame, Fin.snoc]
  have hchain : (Fin.snoc b 0 ∘ p.symm) ᵥ* rationalJacobian H =
      fiberNormal Y hY h ∘ p.symm := by
    have hx : Fin.snoc b 0 ᵥ* rationalJacobian
        (Fin.snoc Y (h : FractionRing (MvPolynomial (Fin 4) K))) =
          fiberNormal Y hY h ∘ p.symm := by
      rw [fiber_jacobian_factorization Y hY h, ← vecMul_vecMul, hframe]
      exact fiberSecondCovector_jacobian p Y hY h c hc
    rw [hchart] at hx
    change Fin.snoc b 0 ᵥ* (rationalJacobian H).submatrix p id = _ at hx
    rw [Matrix.submatrix_vecMul_equiv] at hx
    simpa only [Function.comp_id] using hx
  have hnormal : (fiberNormal Y hY h ∘ p.symm) ᵥ* rationalJacobian H = 0 := by
    have hx := fiberNormal_jacobian_zero Y hY h
    rw [hchart] at hx
    change fiberNormal Y hY h ᵥ* (rationalJacobian H).submatrix p id = 0 at hx
    rw [Matrix.submatrix_vecMul_equiv] at hx
    simpa only [Function.comp_id] using hx
  have hdot := nilpotent_second_covector_kernel_dot_zero _ hN hrank
    (Fin.snoc b 0 ∘ p.symm) (fiberNormal Y hY h ∘ p.symm) u hchain hnormal hu
  rw [comp_equiv_symm_dotProduct] at hdot
  have hb : (∑ i : Fin 3, b i * u (p i.castSucc)) = 0 := by
    simpa [dotProduct, Fin.sum_univ_castSucc, Fin.snoc] using hdot
  change secondFiberInvariant p Y hY h c ∈ (coefficientField (K := K) Y).restrictScalars K
  rw [← tangent_derivation_constants Y hY u hu0 hker]
  change sourceVectorDerivation u (secondFiberInvariant p Y hY h c) = 0
  rw [secondFiberInvariant_deriv p Y hY h c u hker]
  exact hb

/-- The first two expressions in (2.2) are constructed inside the actual
coefficient field for every nilpotent rank-three rational map. -/
theorem exists_first_two_fiber_invariants
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3) :
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
      (h c q : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc))),
      (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3) ∧
        (c : FractionRing (MvPolynomial (Fin 4) K)) =
          firstFiberInvariantInChart p (fun i : Fin 3 => H (p i.castSucc)) hY h ∧
        (q : FractionRing (MvPolynomial (Fin 4) K)) =
          secondFiberInvariant p (fun i : Fin 3 => H (p i.castSucc)) hY h c := by
  obtain ⟨p, hY, h, hh, hc⟩ := exists_firstFiberInvariant_of_nilpotent_rank_three H hN hrank
  let c : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)) :=
    ⟨firstFiberInvariantInChart p (fun i : Fin 3 => H (p i.castSucc)) hY h, hc⟩
  have hq := secondFiberInvariant_mem_of_nilpotent_rank_three H hN hrank p hY h c hh rfl
  let q : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)) :=
    ⟨secondFiberInvariant p (fun i : Fin 3 => H (p i.castSucc)) hY h c, hq⟩
  exact ⟨p, hY, h, c, q, hh, rfl, rfl⟩

/-- The first two invariants under the original polynomial Jacobian and
rational-rank conventions, with every intermediate choice constructed. -/
theorem exists_first_two_fiber_invariants_polynomial
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) :
    let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
      fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => Q (p i.castSucc)))
      (h c q : coefficientField (K := K) (fun i : Fin 3 => Q (p i.castSucc))),
      (h : FractionRing (MvPolynomial (Fin 4) K)) = Q (p 3) ∧
        (c : FractionRing (MvPolynomial (Fin 4) K)) =
          firstFiberInvariantInChart p (fun i : Fin 3 => Q (p i.castSucc)) hY h ∧
        (q : FractionRing (MvPolynomial (Fin 4) K)) =
          secondFiberInvariant p (fun i : Fin 3 => Q (p i.castSucc)) hY h c := by
  let Q : Fin 4 → FractionRing (MvPolynomial (Fin 4) K) :=
    fun i => algebraMap (MvPolynomial (Fin 4) K) _ (H i)
  have hJ : rationalJacobian Q = (jac H).map
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))) :=
    rationalJacobian_polynomial H
  apply exists_first_two_fiber_invariants Q
  · rw [hJ]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K))).mapMatrix
  · rw [hJ]
    exact hrank

end DimensionFourDependence
