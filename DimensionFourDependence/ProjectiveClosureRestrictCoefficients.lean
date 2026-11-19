import DimensionFourDependence.ProjectivePrimeBaseExtension

/-! # Actual projective closure points under restriction of coefficient fields -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {C E F κ σ : Type*} [Field C] [Field E] [Field F] [Field κ]
    [Algebra C E] [Algebra E F] [Algebra C F] [IsScalarTower C E F]
    [Algebra E κ] [Algebra C κ] [IsScalarTower C E κ]

/-- Restricting coefficients preserves every actual projective closure
point. The original coordinate vector is retained in its actual extension
field, and all original homogeneous equations remain valid. -/
theorem projective_closure_point_restrict_coefficients
    (x : σ → F) (z : Option σ → κ) (hz : z ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) z hz ∈ projectiveClosureSet (L := E) x) :
    projectiveFieldPoint (E := C) z hz ∈ projectiveClosureSet (L := C) x := by
  apply projective_field_point_of_extended_cone_relations_mem_original_closure (F := E) x z hz
  have hcone : Ideal.map (MvPolynomial.map (algebraMap C E)) (projectiveConeIdeal (L := C) x) ≤
      projectiveConeIdeal (L := E) x := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    change projectiveConeMap (L := E) x (MvPolynomial.map (algebraMap C E) P) = 0
    change projectiveConeMap (L := C) x P = 0 at hP
    have he : projectiveConeMap (L := E) x (MvPolynomial.map (algebraMap C E) P) =
        projectiveConeMap (L := C) x P :=
      projectiveFieldPointMap_coefficient_extension (fun j : Option σ => j.elim 1 x) P
    rw [he]
    exact hP
  apply hcone.trans
  rw [projectiveClosureSet_eq_zeroLocus_cone] at hpoint
  intro P hP
  exact hpoint hP

end DimensionFourDependence
