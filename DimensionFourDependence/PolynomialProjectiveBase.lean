import DimensionFourDependence.Defs
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # Original coefficient base and properness of projective three-space

The degree-zero ring in the standard four-variable polynomial grading
is explicitly the original coefficient ring. The actual projective
structure morphism to that original base is proper.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [CommRing K]

/-- Constants identify the standard polynomial degree-zero ring with
the original coefficient ring. -/
noncomputable def polynomialProjectiveDegreeZeroEquiv :
    homogeneousSubmodule (Fin 4) K 0 ≃+* K where
  toFun p := constantCoeff p.val
  invFun k := ⟨C k, isHomogeneous_C (Fin 4) k⟩
  left_inv p := by
    apply Subtype.ext
    change C (constantCoeff p.val) = p.val
    exact (totalDegree_eq_zero_iff_eq_C.mp
      ((totalDegree_zero_iff_isHomogeneous (Fin 4)).mpr p.property)).symm
  right_inv k := constantCoeff_C (Fin 4) k
  map_mul' p q := map_mul constantCoeff p.val q.val
  map_add' p q := map_add constantCoeff p.val q.val

/-- The actual coordinate polynomials form a finite generating set
over the standard degree-zero ring. -/
theorem polynomial_projective_finiteType_over_degree_zero :
    Algebra.FiniteType (homogeneousSubmodule (Fin 4) K 0) (MvPolynomial (Fin 4) K) := by
  classical
  let S := Algebra.adjoin (homogeneousSubmodule (Fin 4) K 0)
    (Set.range (X : Fin 4 → MvPolynomial (Fin 4) K))
  have hS : S = ⊤ := by
    apply top_unique
    intro p hp_top
    clear hp_top
    induction p using MvPolynomial.induction_on with
    | C k =>
      exact S.algebraMap_mem ⟨C k, isHomogeneous_C (Fin 4) k⟩
    | add p q hp hq => exact S.add_mem hp hq
    | mul_X p i hp => exact S.mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  refine ⟨⟨Finset.univ.image (X : Fin 4 → MvPolynomial (Fin 4) K), ?_⟩⟩
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using hS

/-- The projective structure morphism to the original coefficient base. -/
noncomputable def polynomialProjectiveToBase :
    AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K) ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero (homogeneousSubmodule (Fin 4) K) ≫
    Spec.map (CommRingCat.ofHom (polynomialProjectiveDegreeZeroEquiv K).symm.toRingHom)

/-- Standard projective three-space is proper over its actual coefficient ring. -/
theorem polynomialProjectiveToBase_isProper : IsProper (polynomialProjectiveToBase K) := by
  let : Algebra.FiniteType (homogeneousSubmodule (Fin 4) K 0) (MvPolynomial (Fin 4) K) :=
    polynomial_projective_finiteType_over_degree_zero K
  have : IsIso (Spec.map
      (CommRingCat.ofHom (polynomialProjectiveDegreeZeroEquiv K).symm.toRingHom)) := by
    change IsIso (Scheme.Spec.mapIso (polynomialProjectiveDegreeZeroEquiv K).symm.toCommRingCatIso.op).hom
    infer_instance
  unfold polynomialProjectiveToBase
  infer_instance

end DimensionFourDependence
