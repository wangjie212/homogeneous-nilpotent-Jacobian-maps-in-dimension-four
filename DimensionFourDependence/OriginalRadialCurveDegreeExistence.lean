import DimensionFourDependence.OriginalFiberChartHilbertInvariance
import DimensionFourDependence.DevelopableFirstInvariant
import DimensionFourDependence.OriginalFiberRadialDegree
import DimensionFourDependence.SpecifiedGraphCoefficientExtension

/-! # Positive original radial curve degree in every independent output chart -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
  (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y₀" p:max => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))

include I hH hd hind hGauss

/-- Every actual independent graph chart of the original developable
map has its own positive radial curve degree. Its existence is derived
from the full fiber and the original nonzero first invariant. -/
theorem original_developable_radial_curve_degree_exists_in_every_output_chart
    (hN : IsNilpotent (jac H)) (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4)) (hY : AlgebraicIndependent K (Y₀ p))
    (h : coefficientField (K := K) (Y₀ p))
    (hh : (h : S₀) = algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p 3))) :
    ∃ D : ℕ, D ≤ 6 ∧ HasCurveHilbertDegree
      (projectiveFieldPointIdeal (E := coefficientField (K := K) (Y₀ p))
        (rationalCoordinate (K := K) (n := 4))).toIdeal D := by
  let HQ : Fin 4 → S₀ := fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)
  have hNQ : IsNilpotent (rationalJacobian HQ) := by
    rw [rationalJacobian_polynomial]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K) S₀).mapMatrix
  have hrankQ : (rationalJacobian HQ).rank = 3 := by
    rw [rationalJacobian_polynomial]
    exact hrank
  obtain ⟨D, hD6, hD⟩ := original_full_fiber_curve_degree_exists_in_every_output_chart
    HQ hrankQ hNQ p hY
  obtain ⟨c, q, k, hc, _hq, _hk⟩ := specified_original_chart_exists_exact_invariant_coefficients
    H hrank p hY hN h hh
  have hc0 : c ≠ 0 := by
    intro hz
    apply I.developable_first_invariant_ne_zero H hd hH hind (by rw [hGauss]) p hY h hh
    rw [← hc, hz]
    rfl
  exact ⟨D, hD6, (actual_first_invariant_radial_curve_degree p (Y₀ p) hY h c hc hc0 D).mp hD⟩

end DimensionFourDependence
