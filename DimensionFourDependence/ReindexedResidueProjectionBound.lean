import DimensionFourDependence.ReindexedOriginalChartSectionBound
import DimensionFourDependence.ResidueProjectionActionCompatibility

/-! # The original-chart section bound from actual residue projection coordinates

An independent pair of original local coordinates, one with
transcendental residue, constructs every rational, polynomial and
infinity action required by the bound. The monic equation, finite field
degree, local base polynomial and both section integralities are all
derived from the original full-fiber-degree hypersurface equation.
-/

namespace DimensionFourDependence

universe u

open MvPolynomial Matrix

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {F B L : Type u} [Field F] [CharZero F]
  [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B] [Algebra F B]
  [Field L] [Algebra F L] [Algebra B L] [IsFractionRing B L] [IsScalarTower F B L]

/-- Original normalized chart coefficients satisfy the hypersurface
degree bound from the actual independent residue projection coordinates.
No rational-field action, polynomial-base center, finite extension,
auxiliary normalized projection chart or section integrality is supplied. -/
theorem original_chart_reindexed_residue_projection_section_order_le_hypersurface_degree
    (hmax : IsLocalRing.maximalIdeal B ≠ ⊥)
    (u w : B) (hu : Transcendental F (IsLocalRing.residue B u))
    (hind : AlgebraicIndependent F ![algebraMap B L u, algebraMap B L w])
    (x : Fin 4 → L) (sectionValue : ProjectiveNormalizedSection (k := F) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hfield : IntermediateField.adjoin F
      (Set.range (fun j => x (s.symm (some j)) / x (s.symm none))) = ⊤)
    (T : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) (r : Fin 3 ≃ Fin 3) (v : L)
    (hcoordinates : (fun i => linearProjectionCoordinate T
      (fun j => x (s.symm (some j)) / x (s.symm none)) (r i)) =
      ![v, algebraMap B L w, algebraMap B L u])
    (g : MvPolynomial (Option (Fin 2)) F) (hg : g ≠ 0)
    (hfull : g.degreeOf none = g.totalDegree)
    (hrelation : MvPolynomial.aeval (fun i : Option (Fin 2) => i.elim v
      (fun j => ![algebraMap B L w, algebraMap B L u] j)) g = 0)
    (b : B) (hb : b ≠ 0)
    (hvalue : (sectionValue.coefficient (s.symm none) : L) = algebraMap B L b)
    (a : ℕ) (horder : b ∈ (IsLocalRing.maximalIdeal B) ^ a) : a ≤ g.totalDegree := by
  let : Algebra (RatFunc F) B := residueParameterFieldAlgebra u hu
  let : Algebra (RatFunc F) L := residueParameterTargetFieldAlgebra (L := L) u hu
  let : Algebra (Polynomial (RatFunc F)) B := residueProjectionPolynomialAlgebra u hu w
  let : Algebra (Polynomial (RatFunc F)) L := residueProjectionPolynomialTargetAlgebra (L := L) u hu w
  let : Algebra (RatFunc (RatFunc F)) L := independentResidueProjectionFieldAlgebra u w hu hind
  let : Algebra (rationalInfinityRing (RatFunc F)) L := rationalInfinityTargetAlgebra (k := RatFunc F)
  let : IsScalarTower F (RatFunc (RatFunc F)) L :=
    independentResidueProjectionFieldAlgebra_original_scalarTower u w hu hind
  let : IsScalarTower F (Polynomial (RatFunc F)) L :=
    residueProjectionPolynomialTargetAlgebra_original_scalarTower (L := L) u hu w
  let : IsScalarTower (Polynomial (RatFunc F)) B L :=
    residueProjectionPolynomialTargetAlgebra_source_scalarTower (L := L) u hu w
  let : IsScalarTower (Polynomial (RatFunc F)) (RatFunc (RatFunc F)) L :=
    independentResidueProjectionFieldAlgebra_polynomial_scalarTower u w hu hind
  let : IsScalarTower (rationalInfinityRing (RatFunc F)) (RatFunc (RatFunc F)) L :=
    rationalInfinityTargetAlgebra_scalarTower (k := RatFunc F) (L := L)
  have hX : algebraMap (RatFunc (RatFunc F)) L RatFunc.X = algebraMap B L w :=
    independentResidueProjectionFieldAlgebra_X u w hu hind
  have hC : algebraMap (RatFunc (RatFunc F)) L (RatFunc.C (RatFunc.X : RatFunc F)) =
      algebraMap B L u := independentResidueProjectionFieldAlgebra_inner_X u w hu hind
  have hcoordinates' : (fun i => linearProjectionCoordinate T
      (fun j => x (s.symm (some j)) / x (s.symm none)) (r i)) =
      ![v, algebraMap (RatFunc (RatFunc F)) L RatFunc.X,
        algebraMap (RatFunc (RatFunc F)) L (RatFunc.C (RatFunc.X : RatFunc F))] := by
    rw [hX, hC]
    exact hcoordinates
  have hrelation' : MvPolynomial.aeval (fun i : Option (Fin 2) => i.elim v
      (fun j => ![algebraMap (RatFunc (RatFunc F)) L RatFunc.X,
        algebraMap (RatFunc (RatFunc F)) L (RatFunc.C (RatFunc.X : RatFunc F))] j)) g = 0 := by
    rw [hX, hC]
    exact hrelation
  exact original_chart_reindexed_section_order_le_hypersurface_degree
    x sectionValue s hbase hfield T r v RatFunc.X hcoordinates' g hg hfull hrelation' hmax
    b hb hvalue a horder

end DimensionFourDependence
