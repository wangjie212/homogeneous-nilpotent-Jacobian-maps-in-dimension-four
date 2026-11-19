import DimensionFourDependence.ProjectiveHomogeneousPullbackCoefficients
import DimensionFourDependence.ProjectiveCoordinateRatioEvaluation
import DimensionFourDependence.OriginalProjectiveChartRing
import DimensionFourDependence.ProjectiveSourceSections
import DimensionFourDependence.ProjectiveCoefficientChartMaps

/-! # Original projective chart polynomials and their actual section pullbacks -/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (C : Type u) [Field C]

/-- Evaluation at the actual original projective coordinate sections
gives an actual regular chart coefficient for every source polynomial. -/
noncomputable def projectiveChartPolynomialSectionHom (a : Fin 4) :
    MvPolynomial (Fin 4) C →+*
      Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C),
        Proj.basicOpen (homogeneousSubmodule (Fin 4) C) (X a)) :=
  MvPolynomial.eval₂Hom
    (projectiveConstantSectionHom C (Proj.basicOpen (homogeneousSubmodule (Fin 4) C) (X a)))
    (projectiveCoordinateRatioSection C a)

/-- Actual geometric chart evaluation sends the entire regular
polynomial section to the original ratio-coordinate polynomial. -/
theorem projectiveChartPolynomialSectionHom_source_value
    {F : Type u} [Field F] [Algebra C F]
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) (P : MvPolynomial (Fin 4) C) :
    projectiveAmbientSectionToSource x a ha (projectiveChartPolynomialSectionHom C a P) =
      aeval (fun i => projectiveChartTransition (C := C) x a i) P := by
  have heq : (projectiveAmbientSectionToSource x a ha).comp
      (projectiveChartPolynomialSectionHom C a) =
        (aeval (fun i => projectiveChartTransition (C := C) x a i)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [projectiveChartPolynomialSectionHom, RingHom.comp_apply, eval₂Hom_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      exact projectiveConstantSectionHom_source_value C x a ha c
    · intro i
      simp only [projectiveChartPolynomialSectionHom, RingHom.comp_apply, eval₂Hom_X',
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      exact projectiveCoordinateRatioSection_source_transition x a ha i
  exact RingHom.congr_fun heq P

/-- The original source section used in the common-factor theorem
is precisely the actual regular polynomial section in the same chart. -/
theorem originalProjectiveAffineSectionEquiv_symm_sourceSection
    (s : Fin 4 ≃ Option (Fin 3)) (P : MvPolynomial (Fin 4) C) :
    (originalProjectiveAffineSectionEquiv (K := C) (s.symm none)).symm
        (projectiveSourceSectionHom s P) = projectiveChartPolynomialSectionHom C (s.symm none) P := by
  apply (originalProjectiveAffineSectionEquiv (K := C) (s.symm none)).injective
  rw [RingEquiv.apply_symm_apply, originalProjectiveAffineSectionEquiv_apply,
    projectiveChartPolynomialSectionHom_source_value]
  apply Subtype.ext
  rw [projectiveSourceSectionHom_source]
  exact (MvPolynomial.comp_aeval_apply
    (fun i => projectiveChartTransition (C := C) (rationalCoordinate (K := C)) (s.symm none) i)
    (projectiveCoordinateChartAlgebra (C := C) (rationalCoordinate (K := C)) (s.symm none)).val P).symm

variable {C} (Y : Scheme.{u})
  (f : Y ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) C))

/-- The actual ratio-polynomial pullback is the pullback of the
actual original projective polynomial section, for every polynomial. -/
theorem projectivePullbackChartPolynomialHom_eq_app (a : Fin 4) (P : MvPolynomial (Fin 4) C) :
    projectivePullbackChartPolynomialHom Y f a P =
      f.app (Proj.basicOpen (homogeneousSubmodule (Fin 4) C) (X a))
        (projectiveChartPolynomialSectionHom C a P) := by
  have heq : projectivePullbackChartPolynomialHom Y f a =
      (f.app (Proj.basicOpen (homogeneousSubmodule (Fin 4) C) (X a))).hom.comp
        (projectiveChartPolynomialSectionHom C a) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [projectivePullbackChartPolynomialHom, projectiveChartPolynomialSectionHom,
        eval₂Hom_C, RingHom.comp_apply, projectivePullbackChartConstantHom]
    · intro i
      simp only [projectivePullbackChartPolynomialHom, projectiveChartPolynomialSectionHom,
        eval₂Hom_X', RingHom.comp_apply]
  exact RingHom.congr_fun heq P

end DimensionFourDependence
