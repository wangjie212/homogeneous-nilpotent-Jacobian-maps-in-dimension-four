import DimensionFourDependence.QuadraticBoundaryChart
import DimensionFourDependence.ParametricGraphHessian
import DimensionFourDependence.SimplePolynomialIntersection

/-! # The original first boundary quadric cuts a doubled coordinate line

The actual rank-one graph Hessian is the square of its normal form,
with its original nonzero denominator retained. In a normalized
normal/ruling chart its first boundary equation is a nonzero scalar
times u^2. Removing this scalar preserves the full pair intersection
ideal with the actual second boundary equation.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {F : Type*} [Field F] {n : ℕ}

/-- The original rank-one quotient Hessian polynomial is the square
of its original normal linear form with the exact denominator scalar. -/
theorem quadraticFormPolynomial_rank_one_square (a : Fin n → F) (N : F) :
    quadraticFormPolynomial (fun i j => -(a i * a j) / N) =
      C (-N⁻¹) * (linearFormPolynomial a) ^ 2 := by
  simp only [quadraticFormPolynomial, linearFormPolynomial, pow_two, div_eq_mul_inv,
    map_mul, map_neg, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The original first boundary equation in the normalized chart
is the exact nonzero-scalar doubled line, before any ideal replacement. -/
theorem rank_one_first_boundary_chart
    (a b w z g : Fin n → F) (N q : F)
    (hab : a ⬝ᵥ b = 0) (haw : a ⬝ᵥ w = 1) (haz : a ⬝ᵥ z = 0) :
    aeval (boundaryAffineChartCoordinate b w z)
      (homogeneousComponent 2 (quadraticFiberPolynomial g (fun i j => -(a i * a j) / N) q)) =
        C ((2 : F)⁻¹ * (-N⁻¹)) * (X (0 : Fin 2)) ^ 2 := by
  rw [quadraticFiberPolynomial_leading_component g (fun i j => -(a i * a j) / N) q, map_mul, aeval_C,
    quadraticFormPolynomial_rank_one_square, map_mul, aeval_C, map_pow,
    boundary_chart_linear_form, hab, haw, haz]
  simp only [MvPolynomial.algebraMap_eq, map_zero, map_one, zero_add, zero_mul, one_mul,
    add_zero, map_mul]
  ring

variable {K : Type*} [Field K] [Algebra K F]

/-- The actual graph gradient constructs the first doubled-line
boundary equation in the original source chart, with no rank-one
coefficient array supplied as an additional hypothesis. -/
theorem parametric_graph_first_boundary_chart
    (p : RatFunc K →ₐ[K] F) (delta : Fin n → Derivation K F F) (y : Fin n → F)
    (hcoord : ∀ i j, delta i (y j) = if j = i then 1 else 0)
    (A : Fin n → RatFunc K)
    (htangent : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ y = 0)
    (hfirst : (fun i => p (rationalParameterDerivative K (A i))) ≠ 0)
    (h : F) (hgradient : ∀ i, delta i h = p (A i))
    (b w z g : Fin n → F) (q : F)
    (hb : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ b = 0)
    (hw : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ w = 1)
    (hz : (fun i => p (rationalParameterDerivative K (A i))) ⬝ᵥ z = 0) :
    aeval (boundaryAffineChartCoordinate b w z)
      (homogeneousComponent 2 (quadraticFiberPolynomial g (derivationHessian delta h) q)) =
        C ((2 : F)⁻¹ * (-(parametricRulingDenominator p A y)⁻¹)) * (X (0 : Fin 2)) ^ 2 := by
  have hB : derivationHessian delta h =
      (fun i j => -(p (rationalParameterDerivative K (A i)) * p (rationalParameterDerivative K (A j))) /
        parametricRulingDenominator p A y) := by
    ext i j
    exact parametric_graph_hessian_formula p delta y hcoord A htangent hfirst h hgradient i j
  rw [hB]
  exact rank_one_first_boundary_chart _ b w z g _ q hb hw hz

omit [Algebra K F] in
/-- Removing the nonzero scalar from the first equation preserves
the entire pair ideal with the actual second boundary polynomial. -/
theorem scaled_coordinate_square_pair_ideal (scalar : F) (hscalar : scalar ≠ 0)
    (P : MvPolynomial (Fin 2) F) :
    Ideal.span ({C scalar * X 0 ^ 2, P} : Set (MvPolynomial (Fin 2) F)) =
      simplePolynomialIntersectionIdeal P := by
  change Ideal.span ({C scalar * X 0 ^ 2, P} : Set (MvPolynomial (Fin 2) F)) = Ideal.span {X 0 ^ 2, P}
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro r (rfl | rfl)
    · exact (Ideal.span ({X 0 ^ 2, P} : Set (MvPolynomial (Fin 2) F))).mul_mem_left _
        (Ideal.subset_span (by simp))
    · exact Ideal.subset_span (by simp)
  · apply Ideal.span_le.mpr
    rintro r (rfl | rfl)
    · have he : C scalar⁻¹ * (C scalar * X (0 : Fin 2) ^ 2) = X 0 ^ 2 := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hscalar, map_one, one_mul]
      have hm : C scalar⁻¹ * (C scalar * X (0 : Fin 2) ^ 2) ∈
          Ideal.span ({C scalar * X 0 ^ 2, P} : Set (MvPolynomial (Fin 2) F)) :=
        (Ideal.span ({C scalar * X 0 ^ 2, P} : Set (MvPolynomial (Fin 2) F))).mul_mem_left (C scalar⁻¹)
          (Ideal.subset_span (by simp))
      rwa [he] at hm
    · exact Ideal.subset_span (by simp)

end DimensionFourDependence
