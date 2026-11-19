import DimensionFourDependence.HomogeneousChartPrime
import DimensionFourDependence.ReducedClosureAffineChart

/-! # The original ratio rings are actual affine scheme charts

The prime of the actual projective generic point is transported through
the canonical homogeneous-localization section isomorphism. Quotienting
those actual sections identifies the inverse open of its reduced closed
scheme with the spectrum of the original source-ratio algebra.
-/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {C F : Type u} [Field C] [Field F] [Algebra C F]

local notation "𝒢" => homogeneousSubmodule (Fin 4) C
local notation "Uₐ" a:max => Proj.basicOpen 𝒢 (X a)
local notation "hUₐ" a:max => Proj.isAffineOpen_basicOpen 𝒢 (X a) (isHomogeneous_X (R := C) a) (by omega)

/-- Quotient sections on the actual projective affine open are exactly
the original source-ratio chart, preserving its source relation prime. -/
noncomputable def projectiveSourceAffineSectionQuotientEquiv
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0)
    (z : ProjectiveSpectrum 𝒢)
    (hrel : z.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval x).toRingHom)
    (hza : X a ∉ z.asHomogeneousIdeal) :
    Γ(AlgebraicGeometry.Proj 𝒢, Uₐ a) ⧸ ((hUₐ a).primeIdealOf ⟨z, hza⟩).asIdeal ≃+*
      projectiveCoordinateChartAlgebra (C := C) x a := by
  let E := (Proj.basicOpenIsoAway 𝒢 (X a) (isHomogeneous_X (R := C) a) (by omega)).commRingCatIsoToRingEquiv
  let p := ((hUₐ a).primeIdealOf ⟨z, hza⟩).asIdeal
  let q := ((Proj.basicOpenIsoSpec 𝒢 (X a) (isHomogeneous_X (R := C) a) (by omega)).hom ⟨z, hza⟩).asIdeal
  have hpq : q = p.comap E.toRingHom := by rfl
  have hmap : q = p.map E.symm.toRingHom := hpq.trans (Ideal.comap_symm E.symm)
  exact (Ideal.quotientEquiv p q E.symm hmap).trans
    (homogeneousProjectiveChartPrimeQuotientEquiv x a ha z hrel hza)

/-- The actual inverse affine open in the global reduced projective
source scheme is the spectrum of its original ratio coordinate ring. -/
noncomputable def projectiveSourceReducedClosureAffineChart
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0)
    (z : ProjectiveSpectrum 𝒢)
    (hrel : z.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval x).toRingHom)
    (hza : X a ∉ z.asHomogeneousIdeal) :
    (reducedPointClosureInclusion (AlgebraicGeometry.Proj 𝒢) z ⁻¹ᵁ Uₐ a).toScheme ≅
      Spec (CommRingCat.of (projectiveCoordinateChartAlgebra (C := C) x a)) :=
  reducedPointClosureAffineChart (AlgebraicGeometry.Proj 𝒢) z ⟨Uₐ a, hUₐ a⟩ hza ≪≫
    Scheme.Spec.mapIso (projectiveSourceAffineSectionQuotientEquiv x a ha z hrel hza).symm.toCommRingCatIso.op

end DimensionFourDependence
