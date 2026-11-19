import DimensionFourDependence.FiberEquationSystem
import DimensionFourDependence.GenericOutputPoint

/-! # The geometric generic fiber equations when the final output is zero -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3300000

variable {K : Type u} [Field K] [CharZero K]
local notation "F" => FractionRing (MvPolynomial (Fin 4) K)
local notation "x" => (rationalCoordinate (K := K) (n := 4))

/-- The nilpotent invariants supply two active equations of degrees one
and two with independent gradients, and a nonzero constant value for
the final source coordinate. -/
structure FixedLastFiberEquations (H : Fin 4 → F) where
  chart : Equiv.Perm (Fin 4)
  chart_last : chart (Fin.last 3) = Fin.last 3
  independent : AlgebraicIndependent K (fun i : Fin 3 => H (chart i.castSucc))
  lastValue : coefficientField (K := K) (fun i : Fin 3 => H (chart i.castSucc))
  lastValue_ne_zero : lastValue ≠ 0
  lastValue_eq : (lastValue : F) = x (Fin.last 3)
  plane : MvPolynomial (Fin 3) (coefficientField (K := K) (fun i : Fin 3 => H (chart i.castSucc)))
  quadric : MvPolynomial (Fin 3) (coefficientField (K := K) (fun i : Fin 3 => H (chart i.castSucc)))
  plane_degree : plane.totalDegree ≤ 1
  quadric_degree : quadric.totalDegree ≤ 2
  plane_zero : aeval (fun i : Fin 3 => x (chart i.castSucc)) plane = 0
  quadric_zero : aeval (fun i : Fin 3 => x (chart i.castSucc)) quadric = 0
  gradients_independent : ∀ s t : F,
    s • (fun i => aeval (fun j : Fin 3 => x (chart j.castSucc)) (pderiv i quadric)) +
      t • (fun i => aeval (fun j : Fin 3 => x (chart j.castSucc)) (pderiv i plane)) = 0 →
      s = 0 ∧ t = 0

/-- The zero last output must be the omitted coordinate in every
independent output chart. All its coefficient derivatives vanish,
lowering the actual quadratic and cubic equations by one degree. -/
theorem nilpotent_rank_three_zero_last_output_constructs_fiber_equations
    (H : Fin 4 → F) (hN : IsNilpotent (rationalJacobian H))
    (hr : (rationalJacobian H).rank = 3) (h₀ : H (Fin.last 3) = 0) :
    Nonempty (FixedLastFiberEquations H) := by
  obtain ⟨p, hY, h, c, q, k, hh, hc, hq, hk⟩ := exists_three_fiber_invariants H hN hr
  let Y : Fin 3 → F := fun i => H (p i.castSucc)
  let L := coefficientField (K := K) Y
  let X₀ : Fin 3 → F := fun i => x (p i.castSucc)
  have hl : p (Fin.last 3) = Fin.last 3 := by
    by_contra he
    have hs : p.symm (Fin.last 3) ≠ Fin.last 3 := by
      intro hs
      exact he ((congrArg p hs).symm.trans (p.apply_symm_apply _))
    obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hs
    have hzero : H (p i.castSucc) = 0 := by
      rw [hi, p.apply_symm_apply, h₀]
    exact hY.transcendental i (by rw [hzero]; exact isAlgebraic_zero)
  have hh₀ : h = (0 : L) := by
    apply Subtype.val_injective
    change (h : F) = 0
    change (h : F) = H (p (Fin.last 3)) at hh
    rw [hh, hl, h₀]
  have hc' : (c : F) = x (Fin.last 3) := by
    have he : firstFiberInvariantInChart p Y hY h = x (Fin.last 3) := by
      rw [hh₀]
      change x (p (Fin.last 3)) - ∑ i : Fin 3,
        (coefficientPartial Y hY i (0 : L) : F) * x (p i.castSucc) = _
      rw [hl]
      simp only [map_zero, ZeroMemClass.coe_zero, zero_mul, Finset.sum_const_zero, sub_zero]
    exact hc.trans he
  have hc₀ : c ≠ 0 := by
    intro hz
    have hcX : x (Fin.last 3) = 0 := by rw [← hc', hz]; rfl
    exact X_ne_zero (Fin.last 3) ((IsFractionRing.injective (MvPolynomial (Fin 4) K) F)
      (hcX.trans (map_zero _).symm))
  let P := quadraticFiberEquation Y hY h c q
  let Q := cubicFiberEquation Y hY h c q k
  have hP : P.totalDegree ≤ 1 := by
    change (quadraticFiberEquation Y hY h c q).totalDegree ≤ 1
    rw [hh₀]
    have hzero : quadraticFiberEquation Y hY (0 : L) c q =
        linearFormPolynomial (coefficientGradient Y hY c) - C q := by
      simp [quadraticFiberEquation, quadraticFiberPolynomial, coefficientHessian, quadraticFormPolynomial]
    rw [hzero]
    exact (totalDegree_sub_C_le _ _).trans (linearFormPolynomial_totalDegree _)
  have hQ : Q.totalDegree ≤ 2 := by
    change (cubicFiberEquation Y hY h c q k).totalDegree ≤ 2
    rw [hh₀]
    have hzero : cubicFiberEquation Y hY (0 : L) c q k =
        linearFormPolynomial (coefficientGradient Y hY q) -
        C ((2 : L)⁻¹) * quadraticFormPolynomial (coefficientHessian Y hY c) - C k := by
      simp [cubicFiberEquation, cubicFiberPolynomial, coefficientCubicTensor, cubicFormPolynomial]
    rw [hzero]
    apply (totalDegree_sub_C_le _ _).trans
    apply (totalDegree_sub _ _).trans
    exact max_le ((linearFormPolynomial_totalDegree _).trans (by decide))
      ((totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact quadraticFormPolynomial_totalDegree _))
  refine ⟨{
    chart := p
    chart_last := hl
    independent := hY
    lastValue := c
    lastValue_ne_zero := hc₀
    lastValue_eq := hc'
    plane := P
    quadric := Q
    plane_degree := hP
    quadric_degree := hQ
    plane_zero := quadraticFiberEquation_aeval_zero p Y hY h c q hq
    quadric_zero := cubicFiberEquation_aeval_zero p Y hY h c q k hk
    gradients_independent := ?_ }⟩
  intro s t hs
  apply fiber_covectors_independent H p hY h c q hh hc hq s t
  change s • (fun i => aeval X₀ (pderiv i Q)) + t • (fun i => aeval X₀ (pderiv i P)) = 0 at hs
  simp only [Q, P, X₀, cubicFiberEquation_gradient_aeval, quadraticFiberEquation_gradient_aeval] at hs
  exact hs

end DimensionFourDependence
