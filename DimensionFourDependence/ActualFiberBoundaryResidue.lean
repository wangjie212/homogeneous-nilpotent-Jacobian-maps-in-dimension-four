import DimensionFourDependence.ActualFiberBoundaryExistence
import DimensionFourDependence.CurveValuationResidueAlgebraic
import DimensionFourDependence.CoefficientCurveField

/-! # The actual boundary residue and its finite coordinate extension -/

namespace DimensionFourDependence

open Matrix MvPolynomial

universe u

set_option quotPrecheck false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hN : IsNilpotent (jac H))
    (hrank : polyRank (jac H) = 3) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "x₀" => fun i : Fin 3 => rationalCoordinate (K := K) (p i.castSucc)

include hY hN hrank

/-- The actual source is a curve field over the actual coefficient
field in every original independent graph chart. -/
theorem actual_fiber_chart_source_trdeg_one : Algebra.trdeg (L) S₀ = 1 := by
  let Q : Fin 4 → S₀ := fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)
  have hQN : IsNilpotent (rationalJacobian Q) := by
    rw [rationalJacobian_polynomial H]
    exact hN.map (algebraMap (MvPolynomial (Fin 4) K) S₀).mapMatrix
  have hQr : (rationalJacobian Q).rank = 3 := by
    rw [rationalJacobian_polynomial H]
    exact hrank
  obtain ⟨u, hu, hker⟩ := matrix_nilpotent_exists_nonzero_kernel _ hQN (by rw [hQr]; decide)
  apply rational_coefficientField_trdeg_eq_one (Y) hY u hu
  funext i
  exact congrFun hker (p i.castSucc)

/-- Every actual nonzero normalized boundary direction has residue
field algebraic over the actual coefficient field, derived from the
original curve dimension and the normalized boundary coordinates. -/
theorem actual_fiber_chart_normalized_boundary_residue_isAlgebraic
    (V : ValuationSubring S₀) [Algebra (L) V] [IsScalarTower (L) V S₀]
    (i : Fin 3) (s : S₀) (z : Option (Fin 3) → V)
    (hz0 : (z none : S₀) = s) (hz : ∀ j, (z (some j) : S₀) = s * (x₀) j)
    (hr0 : IsLocalRing.residue V (z none) = 0)
    (hr1 : IsLocalRing.residue V (z (some i)) = 1) :
    Algebra.IsAlgebraic (L) (IsLocalRing.ResidueField V) :=
  normalized_curve_boundary_residue_isAlgebraic V (x₀) i s z hz0 hz hr0 hr1
    (actual_fiber_chart_source_trdeg_one H hN hrank p hY).le

/-- The normalized boundary coordinates belong to a constructed
finite extension of the entire actual coefficient field. This does
not yet assert algebraicity over the Gauss parameter alone. -/
theorem actual_fiber_boundary_coordinate_field_finite
    (V : ValuationSubring S₀) [Algebra (L) V] [IsScalarTower (L) V S₀]
    (i : Fin 3) (s : S₀) (z : Option (Fin 3) → V)
    (hz0 : (z none : S₀) = s) (hz : ∀ j, (z (some j) : S₀) = s * (x₀) j)
    (hr0 : IsLocalRing.residue V (z none) = 0)
    (hr1 : IsLocalRing.residue V (z (some i)) = 1) :
    Module.Finite (L) (IntermediateField.adjoin (L)
      (Set.range (fun j => IsLocalRing.residue V (z (some j))))) := by
  let : Algebra.IsAlgebraic (L) (IsLocalRing.ResidueField V) :=
    actual_fiber_chart_normalized_boundary_residue_isAlgebraic H hN hrank p hY V i s z hz0 hz hr0 hr1
  exact IntermediateField.finiteDimensional_adjoin (fun a _ =>
    (Algebra.IsAlgebraic.isAlgebraic (R := L) a).isIntegral)

end DimensionFourDependence
