import DimensionFourDependence.ReindexedInfinityGraph
import DimensionFourDependence.FirstInvariantChart

/-! # The actual original first invariant supplies the degree comparison

The first invariant is the graph constant in the original source
function field. Its defining equation supplies the exact graph identity
required by the full graded infinity-section comparison. No graph
equation, degree preservation, or local-to-global comparison is assumed.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] [CharZero K]
    (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K))
    (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y)

/-- The original first invariant expresses the actual original four
source coordinates as the graph over their specified first three. -/
theorem actual_first_fiber_invariant_graph_identity
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p Y hY h) :
    (rationalCoordinate (K := K) (n := 4)) ∘ p =
      affineGraphPoint c (fun i => coefficientPartial Y hY i h)
        (fun i : Fin 3 => rationalCoordinate (K := K) (p i.castSucc)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply, affineGraphPoint, Fin.snoc_last]
    change rationalCoordinate (K := K) (p 3) = (c : FractionRing (MvPolynomial (Fin 4) K)) +
      ∑ j : Fin 3, (coefficientPartial Y hY j h : FractionRing (MvPolynomial (Fin 4) K)) *
        rationalCoordinate (K := K) (p j.castSucc)
    unfold firstFiberInvariantInChart at hc
    linear_combination -hc
  · simp only [Function.comp_apply, affineGraphPoint, Fin.snoc_castSucc]

/-- The original full-fiber Hilbert degree is at most two from its
actual single-point infinity support and the constructed actual projected
infinity-chart local bound. The first invariant derives the graph identity. -/
theorem actual_full_fiber_degree_le_two_of_single_support_chart
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p Y hY h)
    (F : Type*) [Field F] [Algebra (coefficientField (K := K) Y) F]
    {e : ℕ} (he : HasCurveHilbertDegree
      (projectiveConeIdeal (L := coefficientField (K := K) Y) (rationalCoordinate (K := K) (n := 4))) e)
    (s0 : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) F))
    (hsupport : ∀ s : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) F),
      Ideal.map (MvPolynomial.map (algebraMap (coefficientField (K := K) Y) F))
          (projectiveConeIdeal (L := coefficientField (K := K) Y) (rationalCoordinate (K := K) (n := 4))) ⊔
        Ideal.span ({X none} : Set (MvPolynomial (Option (Fin 4)) F)) ≤ s.asHomogeneousIdeal.toIdeal → s = s0)
    (b w z : Fin 3 → F) (hdet : (rulingBoundaryCoordinateMatrix w z b).det ≠ 0)
    (hlocal : HasOriginLocalLengthAtMostTwo
      (extendedProjectiveInfinityChartIdeal (E := coefficientField (K := K) Y)
        (fun i : Fin 3 => rationalCoordinate (K := K) (p i.castSucc)) b w z)) : e ≤ 2 :=
  original_curve_degree_le_two_of_graph_infinity_local_bound p c
    (fun i => coefficientPartial Y hY i h) _ _
    (actual_first_fiber_invariant_graph_identity p Y hY h c hc)
    he s0 hsupport b w z hdet hlocal

end DimensionFourDependence
