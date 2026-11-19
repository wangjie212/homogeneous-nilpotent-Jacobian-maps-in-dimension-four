import DimensionFourDependence.OriginalGraphRootActualDegree
import DimensionFourDependence.OriginalMapIndependentGraphRootData
import DimensionFourDependence.FixedVertexGraphRootActualDegree
import DimensionFourDependence.OriginalMapSimpleRootLocalModel

/-! # The original fixed-vertex map constructs its full-fiber degree bound -/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x" => rationalCoordinate (K := K) (n := 4)
local notation "a" => actualClosedGaussCoefficientHom H I p hY h hh
local notation "A" => closedGaussCoefficientGraphSlope H I p hY h hh e
local notation "y₀" => coefficientCoordinate (K := K) (Y)
local notation "n₀" => parametricRulingDenominator (closedGaussCoefficientParameterHom H I p hY h hh e) (A) (y₀)

include hH hind hGauss

omit p hY h hh e hd in
/-- The original map constructs its own chart, positive integral
full-fiber degree and degree bound two. A nonlinear original full fiber
has degree exactly two and an original-coordinate parabola parametrization.
No finite coefficient field, root data, independence or local model is supplied. -/
theorem original_fixed_vertex_map_constructs_full_fiber_degree_bound
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3) (hd1 : 1 < d)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0) :
    ∃ (p : Equiv.Perm (Fin 4))
      (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        S₀ (H (p i.castSucc))))
      (h c : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        S₀ (H (p i.castSucc))))
      (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p 3)))
      (e : RatFunc K ≃ₐ[K] C₀),
      c ≠ 0 ∧ (c : S₀) = firstFiberInvariantInChart p
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))) hY h ∧
      ∃ eCurve : ℕ, HasCurveHilbertDegree (projectiveConeIdeal («L» := coefficientField (K := K)
        (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))) (x)) eCurve ∧
        eCurve ≤ 2 ∧
        (¬ LiesInAffineLine (E := coefficientField (K := K)
          (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))) (x) →
          eCurve = 2 ∧ LiesInAffineParabola («L» := coefficientField (K := K)
            (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc)))) (x)) := by
  have hd0 : 0 < d := lt_trans Nat.zero_lt_one hd1
  obtain ⟨P⟩ := exists_projective_fiber_equation_witness_polynomial H hN hrank
  let W := P.affine.toFiberEquationWitness
  have hNQ : IsNilpotent (rationalJacobian (fun i => algebraMap (MvPolynomial (Fin 4) K)
      S₀ (H i))) := by
    rw [rationalJacobian_polynomial]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K) S₀).mapMatrix
  have hrankQ : (rationalJacobian (fun i => algebraMap (MvPolynomial (Fin 4) K)
      S₀ (H i))).rank = 3 := by
    rw [rationalJacobian_polynomial]
    exact hrank
  obtain ⟨eCurve, _he6, heCurve⟩ := fiber_witness_full_source_degree _ hNQ hrankQ P
  obtain ⟨h, c, q, k, hh, hc, hq, hk, hc0, _hEuler, _hcEuler, _hHess⟩ :=
    developable_fiber_witness_nonzero_weighted_invariants H hd0 hH hN hrank hind I
      (by rw [hGauss]) W
  obtain ⟨e⟩ := actual_closed_gauss_parameter_rational_function_field H I hGauss
  have hboundary := actual_gauss_boundary_root_forms_exist H hrank I W.chart W.independent h c hh e
    hd0 hH hN hind hGauss hc0 q k hc hq hk
  have hcone := actual_boundary_constructs_finite_independent_fixed_vertex_root_data
    H I W.chart W.independent h hh hH e hd0 hind hGauss hrank hN hd1 hvertex c hc hc0 hboundary
  have hgraph := actual_finite_independent_native_root_data_constructs_exact_graph_root_data
    H I W.chart W.independent h hh hH e hd0 hind hGauss c hc hc0 hcone
  have hupper := actual_finite_independent_graph_root_data_bound_original_full_fiber_degree
    H I W.chart W.independent h hh hH e hd0 hind hGauss hrank hN hd1 hvertex
      c q k hc hq hk hgraph eCurve heCurve
  refine ⟨W.chart, W.independent, h, c, hh, e, hc0, hc, eCurve, heCurve, hupper, ?_⟩
  intro hnonlinear
  exact ⟨actual_nonlinear_full_fiber_hilbert_degree_eq_two H hN hrank W.chart W.independent
      heCurve hnonlinear hupper,
    actual_developable_full_fiber_degree_bound_constructs_parabola H I W.chart W.independent h hh e hGauss
      hd0 hH c q hc0 hc hq heCurve hupper hnonlinear⟩

end DimensionFourDependence
