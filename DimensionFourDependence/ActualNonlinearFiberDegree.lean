import DimensionFourDependence.DegreeOneAffineLine
import DimensionFourDependence.ActualFiberBoundaryResidue
import DimensionFourDependence.FullOutputGeometricFiber

/-! # Exact degree two for an actual nonlinear generic fiber

The original rank-three map supplies a source function field of relative
transcendence degree one over its actual coefficient field. Its original
coordinates generate that field, so one of those coordinates is
transcendental. The proved degree-one affine-line theorem then supplies
the nonlinear degree lower bound, without a chosen curve parameter.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] coefficientFieldScalarTower

set_option quotPrecheck false

variable {K : Type*} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)

include hN hrank hY

/-- An actual original source coordinate is transcendental over the
actual selected coefficient field of the original map. -/
theorem actual_full_fiber_exists_transcendental_coordinate :
    ∃ i : Fin 4, Transcendental (L) (rationalCoordinate (K := K) i) := by
  apply exists_transcendental_coordinate (rationalCoordinate (K := K) (n := 4))
    (rationalSource_adjoin_coordinates_eq_top (L))
  rw [actual_fiber_chart_source_trdeg_one H hN hrank p hY]
  exact one_ne_zero

/-- An actual nonlinear full generic fiber has Hilbert degree at
least two, derived from the original map and its source coordinates. -/
theorem actual_nonlinear_full_fiber_hilbert_degree_at_least_two
    {e : ℕ} (he : HasCurveHilbertDegree
      (projectiveConeIdeal («L» := L) (rationalCoordinate (K := K) (n := 4))) e)
    (hline : ¬ LiesInAffineLine (E := L) (rationalCoordinate (K := K) (n := 4))) : 2 ≤ e := by
  obtain ⟨i, hi⟩ := actual_full_fiber_exists_transcendental_coordinate H hN hrank p hY
  exact nonlinear_curve_hilbert_degree_at_least_two _ i hi he hline

/-- The actual original nonlinear full fiber has degree exactly
two whenever the actual infinity-chart calculation bounds it by two. -/
theorem actual_nonlinear_full_fiber_hilbert_degree_eq_two
    {e : ℕ} (he : HasCurveHilbertDegree
      (projectiveConeIdeal («L» := L) (rationalCoordinate (K := K) (n := 4))) e)
    (hline : ¬ LiesInAffineLine (E := L) (rationalCoordinate (K := K) (n := 4)))
    (hupper : e ≤ 2) : e = 2 :=
  Nat.le_antisymm hupper
    (actual_nonlinear_full_fiber_hilbert_degree_at_least_two H hN hrank p hY he hline)

end DimensionFourDependence
