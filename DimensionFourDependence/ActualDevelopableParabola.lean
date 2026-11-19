import DimensionFourDependence.RankOneQuadricParabola
import DimensionFourDependence.AffineGraphParabola
import DimensionFourDependence.ActualDevelopableGraphEquations
import DimensionFourDependence.OriginalFiberInfinityChartDegree

/-! # The actual original developable fiber is a parabola after the degree bound

Euler weight makes the first invariant's gradient independent of the
actual graph-Hessian normal. The actual rank-one Hessian and second
invariant supply the quadratic equation. Relative algebraic closedness
of the actual coefficient field derives a transcendental normal
coordinate on a nonlinear fiber. Thus its actual Hilbert degree bound
constructs a nondegenerate parabola in all original four coordinates.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

set_option quotPrecheck false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (eParam : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)
local notation "x₃" => fun i : Fin 3 => rationalCoordinate (K := K) (p i.castSucc)
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh eParam
local notation "A₀" => closedGaussCoefficientGraphSlope H I p hY h hh eParam
local notation "a₀" => fun i => (f₀) (rationalParameterDerivative K ((A₀) i))
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (f₀) (A₀) (y₀)

omit [CharZero K] in
/-- The original coefficient field is relatively algebraically
closed in the actual original source field, with actual preimages. -/
theorem actual_coefficient_field_algebraic_value_has_preimage (z : S₀)
    (hz : IsAlgebraic (L) z) : ∃ a : L, algebraMap (L) S₀ a = z := by
  have hbase : IsAlgebraic (IntermediateField.adjoin K (Set.range (Y))) z :=
    hz.restrictScalars _
  exact ⟨⟨z, mem_algebraicClosure_iff.mpr hbase⟩, rfl⟩

/-- Euler weight of the nonzero actual first invariant makes its
gradient independent of the actual rank-one Hessian normal. -/
theorem actual_graph_normal_first_invariant_gradient_independent
    (hGauss : gaussImageDimension H I = 1) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (c : L) (hc0 : c ≠ 0) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h) :
    LinearIndependent (L) ![a₀, coefficientGradient (Y) hY c] := by
  let a : Fin 3 → L := a₀
  change LinearIndependent (L) ![a, coefficientGradient (Y) hY c]
  have ha : a ≠ 0 := actual_closed_gauss_graph_gradient_derivative_ne_zero H I p hY h hh eParam hGauss
  have hay : a ⬝ᵥ (y₀) = 0 := actual_closed_gauss_graph_ruling_equation H I p hY h hh eParam hd hH
  have hgy : coefficientGradient (Y) hY c ⬝ᵥ (y₀) = algebraMap K (L) ((d : K)⁻¹) * c := by
    rw [dotProduct_comm]
    change (∑ i, (y₀) i * coefficientPartial (Y) hY i c) = _
    rw [← coefficientEuler_apply]
    exact firstFiberInvariant_output_weight H hd hH p hY h c hh hc
  have hgy0 : coefficientGradient (Y) hY c ⬝ᵥ (y₀) ≠ 0 := by
    rw [hgy]
    exact mul_ne_zero ((map_ne_zero (algebraMap K (L))).mpr
      (inv_ne_zero (Nat.cast_ne_zero.mpr (show d ≠ 0 by omega)))) hc0
  apply (LinearIndependent.pair_iff' ha).mpr
  intro r hr
  have he := congrArg (fun v : Fin 3 → L => v ⬝ᵥ (y₀)) hr
  change (r • a) ⬝ᵥ (y₀) = coefficientGradient (Y) hY c ⬝ᵥ (y₀) at he
  simp only [smul_dotProduct, hay, smul_eq_mul, mul_zero] at he
  exact hgy0 he.symm

include hh eParam

/-- The actual nonzero first invariant, original second invariant,
actual rank-one graph Hessian and proved degree bound construct a
nondegenerate affine parabola in all original source coordinates. -/
theorem actual_developable_full_fiber_degree_bound_constructs_parabola
    (hGauss : gaussImageDimension H I = 1) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (c q : L) (hc0 : c ≠ 0) (hc : (c : S₀) = firstFiberInvariantInChart p (Y) hY h)
    (hq : (q : S₀) = secondFiberInvariant p (Y) hY h c)
    {eCurve : ℕ} (heCurve : HasCurveHilbertDegree (projectiveConeIdeal («L» := L) (x)) eCurve)
    (hupper : eCurve ≤ 2) (hline : ¬ LiesInAffineLine (E := L) (x)) :
    LiesInAffineParabola («L» := L) (x) := by
  have hx := actual_first_fiber_invariant_graph_identity p (Y) hY h c hc
  have hline3 : ¬ LiesInAffineLine (E := L) (x₃) :=
    fun hy => hline (actual_graph_line_of_projected_line p c (fun i => coefficientPartial (Y) hY i h) _ _ hx hy)
  have hreindex := (curveHilbertDegree_reindex («L» := L) p (x) eCurve).mpr heCurve
  rw [hx] at hreindex
  have he3 := (curveHilbertDegree_graph c (fun i => coefficientPartial (Y) hY i h) (x₃) eCurve).mp hreindex
  have hHess : coefficientHessian (Y) hY h =
      (fun i j => -((a₀) i * (a₀) j) / (n₀)) := by
    funext i j
    exact actual_closed_gauss_graph_hessian_formula H I p hY h hh eParam hGauss hd hH i j
  have hQ : aeval (x₃) (quadraticFiberPolynomial (coefficientGradient (Y) hY c)
      (fun i j => -((a₀) i * (a₀) j) / (n₀)) q) = 0 := by
    rw [← hHess]
    exact quadraticFiberEquation_aeval_zero p (Y) hY h c q hq
  have hpara := rank_one_quadric_degree_bound_constructs_parabola
    (actual_coefficient_field_algebraic_value_has_preimage H p) (a₀)
    (coefficientGradient (Y) hY c)
    (actual_graph_normal_first_invariant_gradient_independent H I p hY h hh eParam hGauss hd hH c hc0 hc)
    (n₀) q (actual_closed_gauss_graph_denominator_ne_zero H I p hY h hh eParam hGauss hd hH)
    (x₃) hQ he3 hupper hline3
  exact actual_graph_parabola_of_projected_parabola p c (fun i => coefficientPartial (Y) hY i h) _ _ hx hpara

end DimensionFourDependence
