import DimensionFourDependence.ExtendedGaussProjectiveSections

/-! # Original projective ratio charts retain their coefficient structure map -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry HomogeneousLocalization CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical affine-source inclusion of a standard projective
open agrees with its homogeneous-localization coordinate inclusion. -/
theorem projective_basicOpen_fromSpec
    (C : Type u) [CommRing C] (a : Fin 4) :
    (Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) C) (X a)
      (isHomogeneous_X (R := C) a) (by omega)).fromSpec =
      Spec.map (Proj.awayToSection (homogeneousSubmodule (Fin 4) C) (X a)) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) C) (X a) (isHomogeneous_X (R := C) a) (by omega) := by
  let U := Proj.basicOpen (homogeneousSubmodule (Fin 4) C) (X a)
  let hU := Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) C) (X a)
    (isHomogeneous_X (R := C) a) (by omega)
  let : IsIso U.toSpecΓ := by change IsIso hU.isoSpec.hom; infer_instance
  apply (cancel_epi U.toSpecΓ).mp
  rw [IsAffineOpen.toSpecΓ_fromSpec, ← Category.assoc]
  change U.ι = (Proj.basicOpenIsoSpec (homogeneousSubmodule (Fin 4) C)
    (X a) (isHomogeneous_X (R := C) a) (by omega)).hom ≫ _
  rw [Proj.awayι, Iso.hom_inv_id_assoc]

/-- The actual ambient projection from any evaluated original ratio
chart is a morphism over the original coefficient field. -/
theorem projective_ratio_chart_to_base
    {C F : Type u} [Field C] [Field F] [Algebra C F]
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) :
    Spec.map (CommRingCat.ofHom (projectiveAmbientSectionToSource (C := C) x a ha)) ≫
        (Proj.isAffineOpen_basicOpen (homogeneousSubmodule (Fin 4) C) (X a)
          (isHomogeneous_X (R := C) a) (by omega)).fromSpec ≫ polynomialProjectiveToBase C =
      Spec.map (CommRingCat.ofHom (algebraMap C (projectiveCoordinateChartAlgebra (C := C) x a))) := by
  let S := projectiveCoordinateChartAlgebra (C := C) x a
  have hc : Proj.awayToSection (homogeneousSubmodule (Fin 4) C) (X a) ≫
      CommRingCat.ofHom (projectiveAmbientSectionToSource (C := C) x a ha) =
      CommRingCat.ofHom (homogeneousCoordinateChartToSource (C := C) x a ha) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro w
    exact projectiveAmbientSectionToSource_awayToSection x a ha w
  rw [projective_basicOpen_fromSpec]
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc, hc]
  unfold polynomialProjectiveToBase
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  apply Subtype.ext
  change homogeneousCoordinateChartEval x a ha
    (Away.mk (homogeneousSubmodule (Fin 4) C) (isHomogeneous_X (R := C) a)
      0 (MvPolynomial.C c) (isHomogeneous_C (Fin 4) c)) = algebraMap C F c
  rw [homogeneousCoordinateChartEval_mk]
  simp only [aeval_C, pow_zero, div_one]

end DimensionFourDependence
