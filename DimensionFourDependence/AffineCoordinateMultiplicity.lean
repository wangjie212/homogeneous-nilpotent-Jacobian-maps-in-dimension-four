import DimensionFourDependence.GeneratedCoordinateFractionField
import DimensionFourDependence.HeightOneResidueCoordinate
import DimensionFourDependence.ThreeCoordinateResidueChoice

/-! # Multiplicity at a height-one normalization center of an affine hypersurface

The original three affine coordinates and their original equation suffice.
At every height-one center in an integral finite-type normalization, the
residue parameter, projection and fiber generator are all constructed.
No projection independence or coordinate transcendence is assumed.
-/

namespace DimensionFourDependence

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k A S B L : Type u} [Field k] [CharZero k]
  [CommRing A] [IsDomain A] [Algebra k A]
  [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S]
  [Algebra A S] [FaithfulSMul A S] [Algebra.IsIntegral A S] [IsScalarTower k A S]
  [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B]
  [Algebra k B] [Algebra A B] [Algebra S B]
  [IsScalarTower k A B] [IsScalarTower A S B]
  [Field L] [Algebra k L] [Algebra A L] [Algebra B L]
  [IsFractionRing A L] [IsFractionRing B L]
  [IsScalarTower k A L] [IsScalarTower k B L] [IsScalarTower A B L]

include L in
/-- At a height-one normalization center, the order of a nonzero
original affine coordinate is at most the total degree of its original
three-variable hypersurface relation. All auxiliary projection and
function-field generation hypotheses are derived from the affine data. -/
theorem affine_hypersurface_normalization_coordinate_order_le_totalDegree
    (x : Option (Option Unit) → A) (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (htr : 2 ≤ Algebra.trdeg k A)
    (hcenter : ((IsLocalRing.maximalIdeal B).under S).height = 1)
    (hz0 : x (some none) ≠ 0)
    (hz : algebraMap A B (x (some none)) ∈ IsLocalRing.maximalIdeal B)
    (f : MvPolynomial (Option (Option Unit)) k) (hf : f ≠ 0)
    (hroot : MvPolynomial.aeval x f = 0)
    (a : ℕ) (horder : algebraMap A B (x (some none)) ∈
      (IsLocalRing.maximalIdeal B) ^ a) : a ≤ f.totalDegree := by
  have hres := height_one_three_coordinates_residue_alternative (S := S) x hx htr hcenter hz
  have hz0' : algebraMap A B (x (some none)) ≠ 0 := by
    intro hzero
    apply hz0
    apply IsFractionRing.injective A L
    rw [IsScalarTower.algebraMap_apply A B L, hzero, map_zero, map_zero]
  have hgen := fraction_field_adjoin_original_coordinates (L := L) x hx
  have hrange : Set.range (fun i => algebraMap A L (x i)) =
      {algebraMap A L (x (some (some ()))), algebraMap A L (x (some none)),
        algebraMap A L (x none)} := by
    ext y
    simp only [Option.range_eq, Set.range_unique, Function.comp_apply,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hrange] at hgen
  let y : Option (Option Unit) → L := fun i => algebraMap B L (algebraMap A B (x i))
  have hvalues : (fun i : Option (Option Unit) =>
      i.elim (y none) (fun j => j.elim (y (some none)) (fun _ => y (some (some ()))))) =
      (fun i => algebraMap A L (x i)) := by
    funext i
    cases i with
    | none => exact (IsScalarTower.algebraMap_apply A B L _).symm
    | some j =>
      cases j with
      | none => exact (IsScalarTower.algebraMap_apply A B L _).symm
      | some j => cases j; exact (IsScalarTower.algebraMap_apply A B L _).symm
  have hrootL : MvPolynomial.aeval (fun i => algebraMap A L (x i)) f = 0 := by
    have h := congrArg (IsScalarTower.toAlgHom k A L) hroot
    rwa [MvPolynomial.comp_aeval_apply, map_zero] at h
  apply three_coordinate_order_le_of_residue_alternative (k := k) (L := L)
    (algebraMap A B (x (some (some ())))) (algebraMap A B (x (some none)))
    (algebraMap A B (x none)) hres hz0' hz _ f hf _ a horder
  · simpa only [← IsScalarTower.algebraMap_apply A B L] using hgen
  · rwa [hvalues]

end DimensionFourDependence
