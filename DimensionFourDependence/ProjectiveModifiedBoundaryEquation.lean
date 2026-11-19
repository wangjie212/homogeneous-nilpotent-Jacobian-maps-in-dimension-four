import DimensionFourDependence.ProjectiveClosureLeadingEquations
import DimensionFourDependence.ModifiedCubicFiberBoundary
import DimensionFourDependence.ParametricGraphBaseChange

/-! # Original equations at arbitrary actual projective boundary points

The modified equation is derived at projective-closure points directly,
without a chosen valuation lift. For an actual parametric graph, the
original equations also derive membership in the ruling and the cubic
factor used in this calculation.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {E F kappa sigma : Type*} [Field E] [Field F] [Field kappa]
    [Algebra E F] [Algebra E kappa] [CharZero E] {n : ℕ}

/-- Both original fiber equations imply the modified boundary
equation at every actual projective point at infinity. -/
theorem projective_closure_modified_cubic_boundary_equation
    (x : sigma → F) (z : Option sigma → kappa) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x)
    (hz0 : z none = 0) (f : Fin n → sigma)
    (a v Lambda : Fin n → E) (B S : Matrix (Fin n) (Fin n) E)
    (T : Fin n → Fin n → Fin n → E) (q k : E)
    (hfactor : cubicFormPolynomial T = linearFormPolynomial Lambda * quadraticFormPolynomial B)
    (hQ : aeval (x ∘ f) (quadraticFiberPolynomial a B q) = 0)
    (hC : aeval (x ∘ f) (cubicFiberPolynomial v S T k) = 0) :
    matrixBilinearPairing (S.map (algebraMap E kappa))
      (fun i => z (some (f i))) (fun i => z (some (f i))) -
      (2 / 3 : kappa) * ((fun i => algebraMap E kappa (Lambda i)) ⬝ᵥ (fun i => z (some (f i)))) *
        ((fun i => algebraMap E kappa (a i)) ⬝ᵥ (fun i => z (some (f i)))) = 0 := by
  let : CharZero kappa := charZero_of_injective_algebraMap (algebraMap E kappa).injective
  have hM : aeval (x ∘ f) (modifiedCubicFiberPolynomial a v Lambda S q k) = 0 := by
    rw [modifiedCubicFiberPolynomial_elimination_identity a v Lambda B S T q k hfactor]
    simp only [map_add, map_mul, hQ, hC, mul_zero, zero_add]
  have he := projectiveClosureSet_projected_leading_equation_at_infinity x z hz hpoint hz0 f
    (modifiedCubicFiberPolynomial a v Lambda S q k) 2
    (modifiedCubicFiberPolynomial_totalDegree a v Lambda S q k) hM
  rw [modifiedCubicFiberPolynomial_leading_component] at he
  simp only [map_add, map_mul, map_neg, aeval_C, linearFormPolynomial, quadraticFormPolynomial,
    map_sum, aeval_X, map_ofNat] at he
  change -(3 : kappa) * matrixBilinearPairing (S.map (algebraMap E kappa))
    (fun i => z (some (f i))) (fun i => z (some (f i))) +
      2 * ((fun i => algebraMap E kappa (Lambda i)) ⬝ᵥ (fun i => z (some (f i)))) *
        ((fun i => algebraMap E kappa (a i)) ⬝ᵥ (fun i => z (some (f i)))) = 0 at he
  linear_combination -(3 : kappa)⁻¹ * he

section Parametric

variable {K G : Type*} [Field K] [CharZero K] [Field G] [Algebra K F] [Algebra F G]

/-- The original affine equations and actual graph data derive
both ruling membership and the modified equation at an actual boundary
point. No Hessian presentation or cubic factor is assumed. -/
theorem parametric_graph_projective_boundary_equations
    (p : RatFunc K →ₐ[K] F) (delta : Fin 3 → Derivation K F F) (y : Fin 3 → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (A : Fin 3 → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (h : F) (hgradient : ∀ i, delta i h = p (A i))
    (x : sigma → G) (z : Option sigma → F) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := F) z hz ∈ projectiveClosureSet (L := F) x)
    (hz0 : z none = 0) (f : Fin 3 → sigma) (c q k : F)
    (hQ : aeval (x ∘ f) (quadraticFiberPolynomial (fun i => delta i c) (derivationHessian delta h) q) = 0)
    (hC : aeval (x ∘ f) (cubicFiberPolynomial (fun i => delta i q)
      (derivationHessian delta c) (derivationCubicTensor delta h) k) = 0) :
    (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ (fun i => z (some (f i))) = 0 ∧
      matrixBilinearPairing (derivationHessian delta c) (fun i => z (some (f i))) (fun i => z (some (f i))) -
        (2 / 3 : F) * (parametricGraphCubicCovector p A y ⬝ᵥ (fun i => z (some (f i)))) *
          ((fun i => delta i c) ⬝ᵥ (fun i => z (some (f i)))) = 0 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hB : (derivationHessian delta h).map (algebraMap F F) =
      fun i j => -(p (rationalParameterDerivative K (A i)) * p (rationalParameterDerivative K (A j))) /
        parametricRulingDenominator p A y := by
    ext i j
    rw [Matrix.map_apply, Algebra.algebraMap_self_apply]
    exact parametric_graph_hessian_formula p delta y hcoord A htangent hfirst h hgradient i j
  have hiso := projective_fiber_closure_quadratic_isotropic x z hz hpoint hz0 f
    (fun i => delta i c) (derivationHessian delta h) q hQ
  rw [hB] at hiso
  refine ⟨(rank_one_quotient_isotropic_iff _ _ _
    (parametric_ruling_denominator_ne_zero p delta y hcoord A htangent hfirst)).mp hiso, ?_⟩
  have hmod := projective_closure_modified_cubic_boundary_equation x z hz hpoint hz0 f
    (fun i => delta i c) (fun i => delta i q) (parametricGraphCubicCovector p A y)
    (derivationHessian delta h) (derivationHessian delta c) (derivationCubicTensor delta h) q k
    (parametric_graph_cubic_polynomial_factorization p delta y hcoord A htangent hfirst h hgradient) hQ hC
  have hmap : (derivationHessian delta c).map (algebraMap F F) = derivationHessian delta c := by
    ext i j
    exact Algebra.algebraMap_self_apply _
  rw [hmap] at hmod
  simpa only [Algebra.algebraMap_self_apply] using hmod

end Parametric

end DimensionFourDependence
