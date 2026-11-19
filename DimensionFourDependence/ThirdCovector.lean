import DimensionFourDependence.SecondInvariant
import DimensionFourDependence.CubicDifferentiation
import DimensionFourDependence.NilpotentCubicFlag

/-! # Differentiating the quadratic equation in Lemma 2.2 -/

namespace DimensionFourDependence

open Matrix

/-- Collect the varying coefficients of a quadratic equation by output
coordinate, including the third derivatives of its Hessian coefficients. -/
theorem collect_quadratic_coefficient_derivatives {F : Type*} [Field F] {n : ℕ}
    (C : Matrix (Fin n) (Fin n) F) (T : Fin n → Fin n → Fin n → F)
    (dy x : Fin n → F) :
    (∑ j, (∑ i, C i j * dy i) * x j) +
      (2 : F)⁻¹ * (∑ j, ∑ k, (∑ i, T i j k * dy i) * x j * x k) =
    ∑ i, ((∑ j, C i j * x j) + (2 : F)⁻¹ * ∑ j, ∑ k, T i j k * x j * x k) * dy i := by
  have hlin : (∑ j, (∑ i, C i j * dy i) * x j) =
      ∑ i, (∑ j, C i j * x j) * dy i := by
    simpa only [zero_mul, Finset.sum_const_zero, zero_add] using
      collect_affine_coefficient_derivatives (fun _ => 0) dy x C
  have hcub : (∑ j, ∑ k, (∑ i, T i j k * dy i) * x j * x k) =
      ∑ i, (∑ j, ∑ k, T i j k * x j * x k) * dy i := by
    simp only [Finset.sum_mul]
    rw [triple_sum_reverse]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hlin, hcub]
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- Differentiate a quadratic fiber equation and move its coefficient
derivatives to the other side. -/
theorem quadratic_fiber_equation_chain_rule {F K : Type*} [Field F] [CharZero F]
    [Field K] [Algebra K F] {n : ℕ} (D : Derivation K F F)
    (g qg dy x : Fin n → F) (H C : Matrix (Fin n) (Fin n) F)
    (T : Fin n → Fin n → Fin n → F) (q : F)
    (hq : q = quadraticExpression g H x) (hH : ∀ i j, H i j = H j i)
    (hDq : D q = ∑ i, qg i * dy i)
    (hDg : ∀ j, D (g j) = ∑ i, C i j * dy i)
    (hDH : ∀ j k, D (H j k) = ∑ i, T i j k * dy i) :
    (∑ i, (g i + ∑ j, H i j * x j) * D (x i)) =
      ∑ i, (qg i - (∑ j, C i j * x j) -
        (2 : F)⁻¹ * ∑ j, ∑ k, T i j k * x j * x k) * dy i := by
  have hd := quadraticExpression_deriv_full D g H x hH
  rw [← hq, hDq] at hd
  simp only [hDg, hDH] at hd
  rw [add_assoc, collect_quadratic_coefficient_derivatives] at hd
  have hs : (∑ i, (qg i - (∑ j, C i j * x j) -
      (2 : F)⁻¹ * ∑ j, ∑ k, T i j k * x j * x k) * dy i) =
      (∑ i, qg i * dy i) -
        ∑ i, ((∑ j, C i j * x j) + (2 : F)⁻¹ * ∑ j, ∑ k, T i j k * x j * x k) * dy i := by
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  rw [hs, hd]
  ring

variable {K : Type*} [Field K] [CharZero K]

/-- The third coefficient derivatives of the last output. -/
noncomputable def fiberThirdDerivative
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) :
    Fin 3 → Fin 3 → Fin 3 → FractionRing (MvPolynomial (Fin 4) K) :=
  fun i j k => (coefficientPartial (K := K) Y hY i (coefficientPartial (K := K) Y hY j
    (coefficientPartial (K := K) Y hY k h)) : FractionRing (MvPolynomial (Fin 4) K))

/-- Swap the first two coefficient-derivative positions. -/
theorem fiberThirdDerivative_swap12
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (i j k : Fin 3) :
    fiberThirdDerivative Y hY h i j k = fiberThirdDerivative Y hY h j i k :=
  congrArg (fun a : coefficientField (K := K) Y => (a : FractionRing (MvPolynomial (Fin 4) K)))
    (coefficientPartials_commute Y hY i j (coefficientPartial (K := K) Y hY k h))

/-- Swap the last two coefficient-derivative positions. -/
theorem fiberThirdDerivative_swap23
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h : coefficientField (K := K) Y) (i j k : Fin 3) :
    fiberThirdDerivative Y hY h i j k = fiberThirdDerivative Y hY h i k j :=
  congrArg (fun a : coefficientField (K := K) Y =>
    (coefficientPartial (K := K) Y hY i a : FractionRing (MvPolynomial (Fin 4) K)))
      (coefficientPartials_commute Y hY j k h)

/-- The covector `a = ∇q - (D²c)x - (1/2)D³h[x,x,·]` from Lemma 2.2. -/
noncomputable def fiberThirdCovector (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c q : coefficientField (K := K) Y) : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) :=
  fun i => (coefficientPartial (K := K) Y hY i q : FractionRing (MvPolynomial (Fin 4) K)) -
    (∑ j, fiberHessian Y hY c i j * rationalCoordinate (K := K) (p j.castSucc)) -
    (2 : FractionRing (MvPolynomial (Fin 4) K))⁻¹ * ∑ j, ∑ k,
      fiberThirdDerivative Y hY h i j k * rationalCoordinate (K := K) (p j.castSucc) *
        rationalCoordinate (K := K) (p k.castSucc)

omit [CharZero K] in
/-- The differential of a reordered coordinate linear expression. -/
theorem chart_coordinate_covector_partial (p : Equiv.Perm (Fin 4))
    (b : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (j : Fin 4) :
    (∑ i : Fin 3, b i * rationalPartial (K := K) j
      (rationalCoordinate (K := K) (p i.castSucc))) = (Fin.snoc b 0 ∘ p.symm) j := by
  have h (k : Fin 4) : (∑ i : Fin 3, b i * rationalPartial (K := K) (p k)
      (rationalCoordinate (K := K) (p i.castSucc))) =
        (Fin.snoc b 0 : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) k := by
    fin_cases k <;> simp [rationalPartial_coordinate, p.injective.eq_iff, Fin.snoc, Fin.sum_univ_succ]
    congr 1
  simpa only [p.apply_symm_apply, Function.comp_apply] using h (p.symm j)

/-- Differentiating the quadratic equation gives `aᵀB = (bᵀ,0)`,
with the original source ordering recorded by `p`. -/
theorem fiberThirdCovector_jacobian (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c q : coefficientField (K := K) Y)
    (hq : (q : FractionRing (MvPolynomial (Fin 4) K)) = secondFiberInvariant p Y hY h c) :
    fiberThirdCovector p Y hY h c q ᵥ* rationalJacobian Y =
      Fin.snoc (fiberSecondCovector p Y hY h c) 0 ∘ p.symm := by
  funext j
  let D := rationalPartial (K := K) j
  have hDq : D (q : FractionRing (MvPolynomial (Fin 4) K)) =
      ∑ i : Fin 3, (coefficientPartial (K := K) Y hY i q : FractionRing (MvPolynomial (Fin 4) K)) * D (Y i) := by
    rw [coefficient_chain_rule Y hY]
    simp only [mul_comm]
  have hDg (k : Fin 3) : D (coefficientPartial (K := K) Y hY k c : FractionRing (MvPolynomial (Fin 4) K)) =
      ∑ i : Fin 3, fiberHessian Y hY c i k * D (Y i) := by
    rw [coefficient_chain_rule Y hY]
    simp only [fiberHessian, Matrix.of_apply, mul_comm]
  have hDH (k l : Fin 3) : D (fiberHessian Y hY h k l) =
      ∑ i : Fin 3, fiberThirdDerivative Y hY h i k l * D (Y i) := by
    change D (coefficientPartial (K := K) Y hY k
      (coefficientPartial (K := K) Y hY l h) : FractionRing (MvPolynomial (Fin 4) K)) = _
    rw [coefficient_chain_rule Y hY]
    simp only [fiberThirdDerivative, mul_comm]
  have hd := quadratic_fiber_equation_chain_rule D
    (fun i => (coefficientPartial (K := K) Y hY i c : FractionRing (MvPolynomial (Fin 4) K)))
    (fun i => (coefficientPartial (K := K) Y hY i q : FractionRing (MvPolynomial (Fin 4) K)))
    (fun i => D (Y i)) (fun i => rationalCoordinate (K := K) (p i.castSucc))
    (fiberHessian Y hY h) (fiberHessian Y hY c) (fiberThirdDerivative Y hY h)
    (q : FractionRing (MvPolynomial (Fin 4) K)) hq (fiberHessian_symmetric Y hY h) hDq hDg hDH
  change (∑ i : Fin 3, fiberSecondCovector p Y hY h c i * D
    (rationalCoordinate (K := K) (p i.castSucc))) =
      (fiberThirdCovector p Y hY h c q ᵥ* rationalJacobian Y) j at hd
  rw [chart_coordinate_covector_partial] at hd
  exact hd.symm

/-- The graph-Jacobian factorization for an arbitrary reordered covector. -/
theorem chart_covector_jacobian
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (h : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3))
    (v : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) :
    (v ∘ p.symm) ᵥ* rationalJacobian H =
      (v ᵥ* fiberFrame (fun i : Fin 3 => H (p i.castSucc)) hY h) ᵥ*
        rationalJacobian (fun i : Fin 3 => H (p i.castSucc)) := by
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i => H (p i.castSucc)
  have hchart : Fin.snoc Y (h : FractionRing (MvPolynomial (Fin 4) K)) = H ∘ p := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
      change (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3)
      exact hh
    · simp only [Fin.snoc_castSucc, Y, Function.comp_apply]
  have hx : v ᵥ* rationalJacobian
      (Fin.snoc Y (h : FractionRing (MvPolynomial (Fin 4) K))) =
        (v ᵥ* fiberFrame Y hY h) ᵥ* rationalJacobian Y := by
    rw [fiber_jacobian_factorization Y hY h, ← vecMul_vecMul]
  rw [hchart] at hx
  change v ᵥ* (rationalJacobian H).submatrix p id = _ at hx
  rw [Matrix.submatrix_vecMul_equiv] at hx
  simpa only [Function.comp_id] using hx

/-- Lift any three-component covector through the graph Jacobian. -/
theorem chart_lifted_covector_jacobian
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (h : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3))
    (a : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) :
    (Fin.snoc a 0 ∘ p.symm) ᵥ* rationalJacobian H =
      a ᵥ* rationalJacobian (fun i : Fin 3 => H (p i.castSucc)) := by
  rw [chart_covector_jacobian H p hY h hh]
  have hframe : Fin.snoc a 0 ᵥ* fiberFrame (fun i : Fin 3 => H (p i.castSucc)) hY h = a := by
    funext i
    simp [vecMul, dotProduct, Fin.sum_univ_castSucc, fiberFrame, Fin.snoc]
  rw [hframe]

/-- The differentiated fiber equations give a three-step covector chain
for the original full Jacobian. -/
theorem fiber_covector_chain
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (h c q : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3))
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) =
      firstFiberInvariantInChart p (fun i : Fin 3 => H (p i.castSucc)) hY h)
    (hq : (q : FractionRing (MvPolynomial (Fin 4) K)) =
      secondFiberInvariant p (fun i : Fin 3 => H (p i.castSucc)) hY h c) :
    let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i => H (p i.castSucc)
    let a := fiberThirdCovector p Y hY h c q
    let b := fiberSecondCovector p Y hY h c
    let ν := fiberNormal Y hY h ∘ p.symm
    (Fin.snoc a 0 ∘ p.symm) ᵥ* rationalJacobian H = Fin.snoc b 0 ∘ p.symm ∧
      (Fin.snoc b 0 ∘ p.symm) ᵥ* rationalJacobian H = ν ∧
      ν ᵥ* rationalJacobian H = 0 ∧ ν ≠ 0 := by
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i => H (p i.castSucc)
  let a := fiberThirdCovector p Y hY h c q
  let b := fiberSecondCovector p Y hY h c
  let ν := fiberNormal Y hY h ∘ p.symm
  change (Fin.snoc a 0 ∘ p.symm) ᵥ* rationalJacobian H = Fin.snoc b 0 ∘ p.symm ∧
    (Fin.snoc b 0 ∘ p.symm) ᵥ* rationalJacobian H = ν ∧ ν ᵥ* rationalJacobian H = 0 ∧ ν ≠ 0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [chart_lifted_covector_jacobian H p hY h hh a]
    exact fiberThirdCovector_jacobian p Y hY h c q hq
  · rw [chart_lifted_covector_jacobian H p hY h hh b]
    exact fiberSecondCovector_jacobian p Y hY h c hc
  · rw [chart_covector_jacobian H p hY h hh (fiberNormal Y hY h),
      fiberNormal_frame_zero, zero_vecMul]
  · intro hz
    have hi := congrFun hz (p (Fin.last 3))
    simp [ν, fiberNormal, Fin.snoc] at hi

/-- The quadratic and cubic fiber gradients are independent, as required
for the complete-intersection argument of Lemma 2.2. -/
theorem fiber_covectors_independent
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => H (p i.castSucc)))
    (h c q : coefficientField (K := K) (fun i : Fin 3 => H (p i.castSucc)))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = H (p 3))
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) =
      firstFiberInvariantInChart p (fun i : Fin 3 => H (p i.castSucc)) hY h)
    (hq : (q : FractionRing (MvPolynomial (Fin 4) K)) =
      secondFiberInvariant p (fun i : Fin 3 => H (p i.castSucc)) hY h c)
    (s t : FractionRing (MvPolynomial (Fin 4) K))
    (hrel : s • fiberThirdCovector p (fun i : Fin 3 => H (p i.castSucc)) hY h c q +
      t • fiberSecondCovector p (fun i : Fin 3 => H (p i.castSucc)) hY h c = 0) :
    s = 0 ∧ t = 0 := by
  let Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K) := fun i => H (p i.castSucc)
  let a := fiberThirdCovector p Y hY h c q
  let b := fiberSecondCovector p Y hY h c
  obtain ⟨ha, hb, hν, hν0⟩ := fiber_covector_chain H p hY h c q hh hc hq
  apply three_step_covectors_independent (rationalJacobian H)
    (Fin.snoc a 0 ∘ p.symm) (Fin.snoc b 0 ∘ p.symm) (fiberNormal Y hY h ∘ p.symm)
    hν0 ha hb hν s t
  funext j
  change s * (Fin.snoc a 0 : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (p.symm j) +
    t * (Fin.snoc b 0 : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (p.symm j) = 0
  refine Fin.lastCases ?_ (fun i => ?_) (p.symm j)
  · simp only [Fin.snoc_last, mul_zero, add_zero]
  · simpa only [Fin.snoc_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      congrFun hrel i

end DimensionFourDependence
