import DimensionFourDependence.ProjectiveNormalizedPrimeCoordinates
import DimensionFourDependence.FiberBoundaryCoefficientExtension

/-! # Normalized primes of the extended closure remain actual original closure points

The specified coefficient maps preserve the homogeneous point line map.
Consequently every prime containing the extended original cone ideal
has normalized coordinates representing an actual point of the original
closure, over the original coefficient field. Coordinate membership in
the prime also determines the zero coordinates of this representative.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Coefficients

variable {E F R sigma : Type*} [Field E] [Field F] [Field R]
    [Algebra E F] [Algebra E R] [Algebra F R] [IsScalarTower E F R]

/-- The actual homogeneous point line map respects the specified
extension of the original polynomial coefficients. -/
theorem projectiveFieldPointMap_coefficient_extension
    (v : sigma → R) (P : MvPolynomial sigma E) :
    projectiveFieldPointMap (E := F) v (MvPolynomial.map (algebraMap E F) P) =
      projectiveFieldPointMap (E := E) v P := by
  have he : ((projectiveFieldPointMap (E := F) v).restrictScalars E).comp
      (MvPolynomial.mapAlgHom (Algebra.ofId E F)) = projectiveFieldPointMap (E := E) v := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [projectiveFieldPointMap, gradeHom]
  exact DFunLike.congr_fun he P

/-- Containing the specified extended cone relations makes a point
an actual point of the original coefficient-field projective closure. -/
theorem projective_field_point_of_extended_cone_relations_mem_original_closure
    {G : Type*} [Field G] [Algebra E G]
    (x : sigma → G) (v : Option sigma → R) (hv : v ≠ 0)
    (hrel : Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ≤
      (projectiveFieldPoint (E := F) v hv).asHomogeneousIdeal.toIdeal) :
    projectiveFieldPoint (E := E) v hv ∈ projectiveClosureSet (L := E) x := by
  rw [projectiveClosureSet_eq_zeroLocus_cone]
  intro P hP
  have hm := hrel (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap E F)) hP)
  change projectiveFieldPointMap (E := F) v (MvPolynomial.map (algebraMap E F) P) = 0 at hm
  change projectiveFieldPointMap (E := E) v P = 0
  rwa [projectiveFieldPointMap_coefficient_extension] at hm

end Coefficients

variable {E F G sigma : Type*} [Field E] [Field F] [Field G] [Algebra E F] [Algebra E G]

/-- Every normalized representative of an actual extended projective
prime is an actual extension-valued point of the original closure. -/
theorem normalized_extended_projective_prime_mem_original_closure
    (x : sigma → G) (z : ProjectiveSpectrum (homogeneousSubmodule (Option sigma) F))
    (hext : Ideal.map (MvPolynomial.map (algebraMap E F)) (projectiveConeIdeal (L := E) x) ≤
      z.asHomogeneousIdeal.toIdeal)
    (a : Option sigma) (ha : X a ∉ z.asHomogeneousIdeal) :
    projectiveFieldPoint (E := E) (projectivePrimeRatioCoordinate z a)
      (projectivePrimeRatioCoordinate_ne_zero z a ha) ∈ projectiveClosureSet (L := E) x := by
  apply projective_field_point_of_extended_cone_relations_mem_original_closure (F := F) x
    (projectivePrimeRatioCoordinate z a) (projectivePrimeRatioCoordinate_ne_zero z a ha)
  rw [projectivePrimeRatioCoordinate_represents z a ha]
  exact hext

omit [Field E] [Field G] [Algebra E F] [Algebra E G] in
/-- An original coordinate in the projective prime is exactly zero
in every normalized prime coordinate field. -/
theorem projectivePrimeRatioCoordinate_zero_of_mem
    {tau : Type*} (z : ProjectiveSpectrum (homogeneousSubmodule tau F)) (a i : tau)
    (hi : X i ∈ z.asHomogeneousIdeal) : projectivePrimeRatioCoordinate z a i = 0 := by
  apply Subtype.ext
  change projectivePrimeCoordinate z i / projectivePrimeCoordinate z a = 0
  rw [(projectivePrimeCoordinate_eq_zero_iff z i).mpr hi, zero_div]

omit [Field E] [Field G] [Algebra E F] [Algebra E G] in
/-- A projective point on the original infinity hyperplane has a
nonzero affine-direction coordinate available for normalization. -/
theorem projective_infinity_prime_exists_direction_coordinate_not_mem
    (z : ProjectiveSpectrum (homogeneousSubmodule (Option sigma) F))
    (hinfinity : X none ∈ z.asHomogeneousIdeal) :
    ∃ a : sigma, X (some a) ∉ z.asHomogeneousIdeal := by
  obtain ⟨a, ha⟩ := projectiveSpectrum_exists_coordinate_not_mem z
  cases a with
  | none => exact (ha hinfinity).elim
  | some a => exact ⟨a, ha⟩

end DimensionFourDependence
