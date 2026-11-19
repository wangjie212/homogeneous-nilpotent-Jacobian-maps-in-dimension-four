import DimensionFourDependence.FiniteNormalization
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finiteness of the glued normalization from its actual affine closures

The relative-normalization construction supplies the overlap maps and
gluing. Finiteness of the integral closures on affine opens makes the
resulting global morphism finite, by the target-local criterion.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness of the actual affine integral closures implies finiteness
of the glued relative normalization morphism. -/
theorem relative_normalization_finite_of_affine_closures_finite
    (hfinite : ∀ U : Y.affineOpens,
      letI := (f.app U.1).hom.toAlgebra
      Module.Finite Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))) :
    IsFinite f.fromNormalization := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _ (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (f.fromNormalization ⁻¹ᵁ U).ι (f.normalizationOpenCover.f U)
    (by simpa using congr($(f.fromNormalization_preimage U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ U.2.isoSpec.hom]
  have hfin : (f.normalizationDiagramMap.app (.op U)).hom.Finite := by
    let := (f.app U).hom.toAlgebra
    exact hfinite U
  convert! (IsFinite.SpecMap_iff _).mpr hfin
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, AlgebraicGeometry.Scheme.Hom.ι_fromNormalization]

end DimensionFourDependence
