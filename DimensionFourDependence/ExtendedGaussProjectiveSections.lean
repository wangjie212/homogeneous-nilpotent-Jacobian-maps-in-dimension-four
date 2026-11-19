import DimensionFourDependence.ExtendedGaussSourceFractions
import DimensionFourDependence.ProjectiveSourceChartMorphism

/-! # The geometric projective section map agrees with the original source map

Coefficient pullback on the actual projective chart sections agrees
with original source-ratio evaluation. The original tensor coordinate
identification therefore retains that geometric source pullback.
-/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Evaluation of the actual section represented by a homogeneous
fraction recovers that original fraction's source value. -/
theorem projectiveAmbientSectionToSource_awayToSection
    {C F : Type u} [Field C] [Field F] [Algebra C F]
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0)
    (w : Away (homogeneousSubmodule (Fin 4) C) (X a)) :
    projectiveAmbientSectionToSource x a ha
      ((Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) C) (X a)
        (isHomogeneous_X (R := C) a) (by omega)).hom w) =
      homogeneousCoordinateChartToSource x a ha w := by
  change homogeneousCoordinateChartToSource x a ha
    (((Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) C) (X a)
      (isHomogeneous_X (R := C) a) (by omega)).commRingCatIsoToRingEquiv).symm
      ((Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) C) (X a)
        (isHomogeneous_X (R := C) a) (by omega)).commRingCatIsoToRingEquiv w)) = _
  rw [RingEquiv.symm_apply_apply]

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "zₑ" => primeQuotientCoordinate (extendedClosedGaussPencilIdeal H I E)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "Uₖ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none))
local notation "Uₑ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X (s.symm none))
local notation "fₑ" => extendedClosedGaussSourceCoefficientHom H I E
local notation "σₑ" => polynomialProjectiveCoefficientMap fₑ
local notation "hU" => le_of_eq
  (Eq.symm (polynomialProjectiveCoefficientMap_preimage_basicOpen fₑ (s.symm none)))

include hH e in
/-- The actual projective coefficient morphism's section pullback
agrees with the specified original source-chart evaluation. -/
theorem extendedClosedGaussProjectiveSection_coefficient_compatibility
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K), Uₖ)) :
    projectiveAmbientSectionToSource (C := E) zₑ (s.symm none)
        (extendedClosedGaussRatioCoordinate_ne_zero H I E _)
        ((σₑ).appLE Uₖ Uₑ hU r) =
      extendedClosedGaussSourceChartHom H I E s
        (projectiveAmbientSectionToSource (C := K) x₀ (s.symm none)
          (source_rationalCoordinate_ne_zero _) r) := by
  let a := s.symm none
  let kIso := Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) K) (X a)
    (isHomogeneous_X (R := K) a) (by omega)
  obtain ⟨w, rfl⟩ := kIso.commRingCatIsoToRingEquiv.surjective r
  have hs := ConcreteCategory.congr_hom
    (polynomialProjectiveCoefficientMap_awayToSection fₑ a) w
  change (σₑ).appLE Uₖ Uₑ hU (kIso.hom w) =
    (Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) E) (X a)
      (isHomogeneous_X (R := E) a) (by omega)).hom (polynomialCoefficientAwayHom fₑ a w) at hs
  rw [show kIso.commRingCatIsoToRingEquiv w = kIso.hom w from rfl]
  rw [hs, projectiveAmbientSectionToSource_awayToSection,
    projectiveAmbientSectionToSource_awayToSection]
  exact (extendedClosedGaussSourceChartHom_homogeneous_fraction H I E hH e s w).symm

/-- The original tensor coordinates of an actual original projective
source section. -/
noncomputable def extendedClosedGaussProjectiveSourceSectionHom :
    Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K), Uₖ) →+* S₀ ⊗[C₀] E :=
  (extendedClosedGaussTensorSourceHom H I E s).comp
    (projectiveAmbientSectionToSource (C := K) x₀ (s.symm none)
      (source_rationalCoordinate_ne_zero _))

/-- The actual original tensor chart retains the geometric pullback
of every original projective source section. -/
theorem extendedClosedGaussProjectiveSourceSectionHom_compatibility
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K), Uₖ)) :
    extendedClosedGaussRatioCoordinateEquiv H I E hH e s
        (extendedClosedGaussProjectiveSourceSectionHom H I E s r) =
      projectiveAmbientSectionToSource (C := E) zₑ (s.symm none)
        (extendedClosedGaussRatioCoordinate_ne_zero H I E _)
        ((σₑ).appLE Uₖ Uₑ hU r) :=
  (extendedClosedGaussSourceChartHom_compatibility H I E hH e s _).trans
    (extendedClosedGaussProjectiveSection_coefficient_compatibility H I E hH e s r).symm

end DimensionFourDependence
