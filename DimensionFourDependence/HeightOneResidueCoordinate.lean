import DimensionFourDependence.AffineMaximalHeight
import DimensionFourDependence.TranscendentalResidueCoordinate

/-! # Height-one normalization centers supply an original residue parameter -/

namespace DimensionFourDependence

universe u

variable {k A S B : Type u} {σ : Type*} [Field k]
  [CommRing A] [Algebra k A]
  [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S]
  [Algebra A S] [FaithfulSMul A S] [Algebra.IsIntegral A S] [IsScalarTower k A S]
  [CommRing B] [IsLocalRing B] [Algebra k B] [Algebra A B] [Algebra S B]
  [IsScalarTower k A B] [IsScalarTower A S B]

/-- At every height-one center on an integral finite-type normalization
of a surface algebra, one original coordinate has transcendental residue.
The nonclosedness and the residue parameter are conclusions. -/
theorem height_one_integral_extension_has_transcendental_coordinate
    (x : σ → A) (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (htr : 2 ≤ Algebra.trdeg k A)
    (hcenter : ((IsLocalRing.maximalIdeal B).under S).height = 1) :
    ∃ i, Transcendental k (IsLocalRing.residue B (algebraMap A B (x i))) := by
  have htrS : 2 ≤ Algebra.trdeg k S := htr.trans
    (trdeg_le_of_injective (IsScalarTower.toAlgHom k A S)
      (FaithfulSMul.algebraMap_injective A S))
  have hnot := height_one_prime_not_isMaximal_finiteType (k := k) htrS
    ((IsLocalRing.maximalIdeal B).under S) hcenter
  exact exists_transcendental_residue_coordinate_of_integral_extension
    (S := S) x hx hnot

/-- For three original affine coordinates, the vanishing coordinate
cannot be the transcendental residue parameter. One of the other two is. -/
theorem height_one_three_coordinates_residue_alternative
    (x : Option (Option Unit) → A) (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (htr : 2 ≤ Algebra.trdeg k A)
    (hcenter : ((IsLocalRing.maximalIdeal B).under S).height = 1)
    (hz : algebraMap A B (x (some none)) ∈ IsLocalRing.maximalIdeal B) :
    Transcendental k (IsLocalRing.residue B (algebraMap A B (x (some (some ()))))) ∨
      Transcendental k (IsLocalRing.residue B (algebraMap A B (x none))) := by
  obtain ⟨i, hi⟩ := height_one_integral_extension_has_transcendental_coordinate
    (S := S) x hx htr hcenter
  cases i with
  | none => exact Or.inr hi
  | some j =>
    cases j with
    | none =>
      have hzero := IsLocalRing.residue_eq_zero_iff _ |>.mpr hz
      rw [hzero] at hi
      exact (hi (isAlgebraic_zero (R := k))).elim
    | some j => cases j; exact Or.inl hi

end DimensionFourDependence
