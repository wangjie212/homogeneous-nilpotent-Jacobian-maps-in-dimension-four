import DimensionFourDependence.ProjectiveSourceSchemeChart
import DimensionFourDependence.ReducedClosureChartMorphism

/-! # Projective source-ratio charts retain the actual projective inclusion

The affine quotient identifications evaluate the original homogeneous
fractions at their source ratios. Their scheme charts therefore commute
with the actual reduced projective closed immersion.
-/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C F : Type u} [Field C] [Field F] [Algebra C F]

local notation "𝒢" => homogeneousSubmodule (Fin 4) C
local notation "Uₐ" a:max => Proj.basicOpen 𝒢 (X a)
local notation "hUₐ" a:max => Proj.isAffineOpen_basicOpen 𝒢 (X a) (isHomogeneous_X (R := C) a) (by omega)

/-- The actual ambient projective affine sections evaluate at the
original source ratios through the canonical homogeneous localization. -/
noncomputable def projectiveAmbientSectionToSource
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) :
    Γ(AlgebraicGeometry.Proj 𝒢, Uₐ a) →+*
      projectiveCoordinateChartAlgebra (C := C) x a :=
  (homogeneousCoordinateChartToSource x a ha).comp
    (Proj.basicOpenIsoAway 𝒢 (X a) (isHomogeneous_X (R := C) a) (by omega)).symm.commRingCatIsoToRingEquiv.toRingHom

/-- The affine prime quotient evaluates an actual homogeneous fraction
at its original source-coordinate values. -/
theorem homogeneousProjectiveChartPrimeQuotientEquiv_mk
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0)
    (z : ProjectiveSpectrum 𝒢)
    (hrel : z.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval x).toRingHom)
    (hza : X a ∉ z.asHomogeneousIdeal) (w : Away 𝒢 (X a)) :
    homogeneousProjectiveChartPrimeQuotientEquiv x a ha z hrel hza
      (Ideal.Quotient.mk
        (((Proj.basicOpenIsoSpec 𝒢 (X a) (isHomogeneous_X (R := C) a) (by omega)).hom
          ⟨z, hza⟩).asIdeal) w) = homogeneousCoordinateChartToSource x a ha w := by
  simp only [homogeneousProjectiveChartPrimeQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- Quotienting actual projective sections retains precisely the
specified original source-ratio evaluation map. -/
theorem projectiveSourceAffineSectionQuotientEquiv_mk
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0)
    (z : ProjectiveSpectrum 𝒢)
    (hrel : z.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval x).toRingHom)
    (hza : X a ∉ z.asHomogeneousIdeal)
    (r : Γ(AlgebraicGeometry.Proj 𝒢, Uₐ a)) :
    projectiveSourceAffineSectionQuotientEquiv x a ha z hrel hza
      (Ideal.Quotient.mk ((hUₐ a).primeIdealOf ⟨z, hza⟩).asIdeal r) =
      projectiveAmbientSectionToSource x a ha r := by
  simp only [projectiveSourceAffineSectionQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotientEquiv_mk]
  rfl

/-- The actual source-ratio chart commutes with its original global
projective inclusion, through evaluation of the actual ambient sections. -/
theorem projectiveSourceReducedClosureAffineChart_inv_to_ambient
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0)
    (z : ProjectiveSpectrum 𝒢)
    (hrel : z.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval x).toRingHom)
    (hza : X a ∉ z.asHomogeneousIdeal) :
    (projectiveSourceReducedClosureAffineChart x a ha z hrel hza).inv ≫
        (reducedPointClosureInclusion (AlgebraicGeometry.Proj 𝒢) z ⁻¹ᵁ Uₐ a).ι ≫
        reducedPointClosureInclusion (AlgebraicGeometry.Proj 𝒢) z =
      Spec.map (CommRingCat.ofHom (projectiveAmbientSectionToSource x a ha)) ≫
        (hUₐ a).fromSpec := by
  let b := projectiveSourceAffineSectionQuotientEquiv x a ha z hrel hza
  have hb : CommRingCat.ofHom (Ideal.Quotient.mk ((hUₐ a).primeIdealOf ⟨z, hza⟩).asIdeal) ≫
        CommRingCat.ofHom b.toRingHom =
      CommRingCat.ofHom (projectiveAmbientSectionToSource x a ha) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact projectiveSourceAffineSectionQuotientEquiv_mk x a ha z hrel hza r
  have h := reducedPointClosureAffineChart_inv_to_ambient
    (AlgebraicGeometry.Proj 𝒢) z ⟨Uₐ a, hUₐ a⟩ hza
  have h' := congrArg (fun k => Spec.map (CommRingCat.ofHom b.toRingHom) ≫ k) h
  rw [← Spec.map_comp_assoc, hb] at h'
  convert! h' using 1

end DimensionFourDependence
