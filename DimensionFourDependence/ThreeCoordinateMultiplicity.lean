import DimensionFourDependence.HypersurfaceLocalMultiplicity
import DimensionFourDependence.ResidueCoordinateProjection
import DimensionFourDependence.ProjectionFieldGenerator

/-! # The multiplicity bound from the three original coordinate functions

A transcendental residue coordinate and a nonzero vanishing coordinate
construct the independent projection. If the three original coordinates
generate the function field, the third one automatically generates its
fiber extension. The original hypersurface equation then bounds the
vanishing coordinate's order, without additional projection assumptions.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k B L : Type*} [Field k] [CharZero k]
  [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B] [Algebra k B]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra k L] [IsScalarTower k B L]

/-- The original three-coordinate hypersurface relation bounds every
order of the nonzero vanishing coordinate. The projection field, its
independence, its fiber generator and its finite degree are constructed. -/
theorem three_coordinate_hypersurface_order_le_totalDegree
    (u z v : B) (hu : Transcendental k (IsLocalRing.residue B u))
    (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B)
    (hgen : IntermediateField.adjoin k
      {algebraMap B L u, algebraMap B L z, algebraMap B L v} = ⊤)
    (f : MvPolynomial (Option (Option Unit)) k) (hf : f ≠ 0)
    (hroot : MvPolynomial.aeval (fun i => i.elim (algebraMap B L v)
      (fun j => j.elim (algebraMap B L z) (fun _ => algebraMap B L u))) f = 0)
    (a : ℕ) (horder : z ∈ (IsLocalRing.maximalIdeal B) ^ a) :
    a ≤ f.totalDegree := by
  let C := RatFunc k
  let T := FractionRing (Polynomial C)
  letI : Algebra C B := residueParameterFieldAlgebra u hu
  letI : Algebra C L := residueParameterTargetFieldAlgebra (L := L) u hu
  letI : IsScalarTower C B L :=
    residueParameterTargetFieldAlgebra_scalarTower (L := L) u hu
  letI : IsScalarTower k C L :=
    residueParameterTargetFieldAlgebra_base_scalarTower (L := L) u hu
  letI : Algebra T L := residueCoordinateProjectionAlgebra (L := L) u hu z hz0 hz
  letI : IsScalarTower k T L :=
    residueCoordinateProjection_base_scalarTower (L := L) u hu z hz0 hz
  have hcoords := residueCoordinateProjection_coordinates (L := L) u hu z hz0 hz
  have hv : IntermediateField.adjoin T {algebraMap B L v} = ⊤ :=
    projection_field_generator_of_three_coordinates
      (algebraMap B L u) (algebraMap B L z) (algebraMap B L v) hgen
      ⟨twoParameterProjectionCoordinates k (some ()), hcoords (some ())⟩
      ⟨twoParameterProjectionCoordinates k none, hcoords none⟩
  have hroot' : MvPolynomial.aeval (fun i => i.elim (algebraMap B L v)
      (fun j => algebraMap T L (twoParameterProjectionCoordinates k j))) f = 0 := by
    have heq : (fun i : Option (Option Unit) => i.elim (algebraMap B L v)
        (fun j => algebraMap T L (twoParameterProjectionCoordinates k j))) =
        (fun i => i.elim (algebraMap B L v)
          (fun j => j.elim (algebraMap B L z) (fun _ => algebraMap B L u))) := by
      funext i
      cases i with
      | none => rfl
      | some j => exact hcoords j
    rw [heq]
    exact hroot
  exact local_coordinate_hypersurface_order_le_totalDegree (k := k) (C := C) (L := L)
    z hz0 hz (twoParameterProjectionCoordinates k)
    (twoParameterProjectionCoordinates_algebraicIndependent k)
    (algebraMap B L v) hv f hf hroot' a horder

end DimensionFourDependence
