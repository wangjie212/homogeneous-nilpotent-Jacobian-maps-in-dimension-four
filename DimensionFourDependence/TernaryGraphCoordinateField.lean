import DimensionFourDependence.TernaryGraphPlaneInvariant
import DimensionFourDependence.FiberCoordinateField

/-! # The function field of the projected ternary curve -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]
local notation "F" => FractionRing (MvPolynomial (Fin 3) K)
local notation "x" => (rationalCoordinate (K := K) (n := 3))

/-- The actual source field has relative transcendence degree one over
the coefficient field of an independent pair. -/
theorem ternary_coefficientField_trdeg_eq_one
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y) :
    Algebra.trdeg (coefficientField (K := K) Y) F = 1 := by
  apply coefficientField_trdeg_eq_one Y (ternaryJacobianDerivation (Y 0) (Y 1))
    (sourceVectorDerivation_ne_zero _ (ternaryJacobianDirection_ne_zero Y hY))
    (ternaryJacobianDerivation_kills_pair Y)
  apply relative_trdeg_le_one_of_independent_outputs Y hY
  rw [rationalSource_trdeg_eq (n := 3)]
  norm_num

/-- The exact first plane equation recovers the last source coordinate
from the first two over the actual coefficient field. -/
theorem ternary_graph_coordinate_field_eq_top
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (w s : coefficientField (K := K) Y) (hs : (s : F) = ternaryGraphPlaneValue Y hY w) :
    IntermediateField.adjoin (coefficientField (K := K) Y)
      (Set.range (fun i : Fin 2 => x i.castSucc)) = ⊤ := by
  let L := coefficientField (K := K) Y
  let : IsScalarTower K L F := coefficientFieldScalarTower Y
  let E := IntermediateField.adjoin L (Set.range (fun i : Fin 2 => x i.castSucc))
  have hx (i : Fin 2) : x i.castSucc ∈ E := IntermediateField.subset_adjoin L _ ⟨i, rfl⟩
  have hlast : x 2 ∈ E := by
    have hp (i : Fin 2) : ternaryGraphGradient Y hY w i ∈ E :=
      E.algebraMap_mem (coefficientPartial Y hY i w)
    have h : x 2 = (s : F) + ternaryGraphGradient Y hY w 0 * x 0 +
        ternaryGraphGradient Y hY w 1 * x 1 := by
      change (s : F) = x 2 - ternaryGraphGradient Y hY w 0 * x 0 -
        ternaryGraphGradient Y hY w 1 * x 1 at hs
      linear_combination -hs
    rw [h]
    exact E.add_mem (E.add_mem (E.algebraMap_mem s) (E.mul_mem (hp 0) (hx 0)))
      (E.mul_mem (hp 1) (hx 1))
  have htop := rationalSource_field_eq_top_of_coordinates (E.restrictScalars K) (by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hlast
    · exact hx j)
  apply top_unique
  intro f _
  change f ∈ E.restrictScalars K
  rw [htop]
  trivial

end DimensionFourDependence
