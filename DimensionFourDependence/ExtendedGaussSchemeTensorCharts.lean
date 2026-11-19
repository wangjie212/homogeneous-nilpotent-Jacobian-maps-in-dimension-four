import DimensionFourDependence.ExtendedGaussPencilScheme
import DimensionFourDependence.ExtendedGaussRatioCoordinates
import DimensionFourDependence.ProjectiveSourceSchemeChart
import DimensionFourDependence.NormalizationAffineCoordinateChart

/-! # Original tensor-chart primes on the global extended pencil normalization

After algebraic coefficient extension, the original tensor ratio ring is
an actual affine chart of the constructed extended pencil scheme. Its
canonical normalization is the actual inverse chart in the normalization
formed after extension. Each of its primes gives a global point with the
same prime localization as its global stalk.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" s:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm s none)
local notation "Pₑ" => extendedClosedGaussPencilIdeal H I E

/-- The original coordinate chart on the actual extended projective pencil. -/
noncomputable def extendedClosedGaussPencilChartOpen (s : Fin 4 ≃ Option (Fin 3)) :
    (extendedClosedGaussPencilScheme H I E hH e).Opens :=
  extendedClosedGaussPencilSchemeInclusion H I E hH e ⁻¹ᵁ
    Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X (s.symm none))

/-- The existing original tensor ratio ring is an actual chart of
the global projective pencil after coefficient extension. -/
noncomputable def extendedClosedGaussPencilTensorChartIso (s : Fin 4 ≃ Option (Fin 3)) :
    (extendedClosedGaussPencilChartOpen H I E hH e s).toScheme ≅
      Spec (CommRingCat.of (S₀ s ⊗[C₀] E)) := by
  let z := primeQuotientCoordinate Pₑ
  let q := extendedClosedGaussPencilGenericPoint H I E hH e
  have hrel : q.asHomogeneousIdeal.toIdeal = RingHom.ker (aeval z).toRingHom :=
    (extendedClosedGaussRatioCoordinate_relations H I E).symm
  exact projectiveSourceReducedClosureAffineChart (C := E) z (s.symm none)
      (extendedClosedGaussRatioCoordinate_ne_zero H I E (s.symm none)) q hrel
      (extendedClosedGaussPencilIdeal_X_not_mem H I E (s.symm none)) ≪≫
    Scheme.Spec.mapIso (extendedClosedGaussRatioCoordinateEquiv H I E hH e s).toCommRingCatIso.op

/-- These original tensor charts are affine opens of the actual extended pencil. -/
theorem extendedClosedGaussPencilChartOpen_isAffineOpen (s : Fin 4 ≃ Option (Fin 3)) :
    IsAffineOpen (extendedClosedGaussPencilChartOpen H I E hH e s) :=
  IsAffine.of_isIso (extendedClosedGaussPencilTensorChartIso H I E hH e s).hom

/-- Every original extended tensor chart is a nonempty actual source open. -/
theorem extendedClosedGaussPencilChartOpen_nonempty (s : Fin 4 ≃ Option (Fin 3)) :
    Nonempty (extendedClosedGaussPencilChartOpen H I E hH e s) := by
  let b := extendedClosedGaussRatioCoordinateEquiv H I E hH e s
  let : IsDomain (S₀ s ⊗[C₀] E) := Function.Injective.isDomain b b.injective
  exact ⟨(extendedClosedGaussPencilTensorChartIso H I E hH e s).inv
    (⊥ : PrimeSpectrum (S₀ s ⊗[C₀] E))⟩

/-- The actual extended scheme's affine sections are the existing
tensor chart ring in the original local-model tensor order. -/
noncomputable def extendedClosedGaussPencilTensorChartSectionEquiv (s : Fin 4 ≃ Option (Fin 3)) :
    Γ(extendedClosedGaussPencilScheme H I E hH e, extendedClosedGaussPencilChartOpen H I E hH e s) ≃+*
      S₀ s ⊗[C₀] E :=
  ((extendedClosedGaussPencilChartOpen H I E hH e s).topIso.symm ≪≫
    (Scheme.Γ.mapIso (extendedClosedGaussPencilTensorChartIso H I E hH e s).op).symm ≪≫
    Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv

/-- The inverse original coordinate open on the normalization formed after extension. -/
noncomputable def extendedClosedGaussNormalizationChartOpen (s : Fin 4 ≃ Option (Fin 3)) :
    (extendedClosedGaussNormalizationScheme H I E hH e).Opens :=
  extendedClosedGaussNormalizationSchemeMap H I E hH e ⁻¹ᵁ extendedClosedGaussPencilChartOpen H I E hH e s

/-- Normalization after extension has the original canonical tensor
normalization as its actual affine inverse chart. -/
noncomputable def extendedClosedGaussNormalizationTensorChartIso (s : Fin 4 ≃ Option (Fin 3)) :
    (extendedClosedGaussNormalizationChartOpen H I E hH e s).toScheme ≅
      Spec (CommRingCat.of (normalizationRing (S₀ s ⊗[C₀] E))) := by
  let : IsIntegral (extendedClosedGaussPencilScheme H I E hH e) :=
    extendedClosedGaussPencilScheme_isIntegral H I E hH e
  let : Nonempty (extendedClosedGaussPencilChartOpen H I E hH e s) :=
    extendedClosedGaussPencilChartOpen_nonempty H I E hH e s
  let b := extendedClosedGaussRatioCoordinateEquiv H I E hH e s
  let : IsDomain (S₀ s ⊗[C₀] E) := Function.Injective.isDomain b b.injective
  exact integralSchemeNormalizationCoordinateChart (extendedClosedGaussPencilScheme H I E hH e)
    ⟨extendedClosedGaussPencilChartOpen H I E hH e s,
      extendedClosedGaussPencilChartOpen_isAffineOpen H I E hH e s⟩
    (S₀ s ⊗[C₀] E) (extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s)

/-- The original tensor normalization ring's actual chart inclusion into the global scheme. -/
noncomputable def extendedClosedGaussNormalizationTensorChartInclusion (s : Fin 4 ≃ Option (Fin 3)) :
    Spec (CommRingCat.of (normalizationRing (S₀ s ⊗[C₀] E))) ⟶
      extendedClosedGaussNormalizationScheme H I E hH e :=
  (extendedClosedGaussNormalizationTensorChartIso H I E hH e s).inv ≫
    (extendedClosedGaussNormalizationChartOpen H I E hH e s).ι

/-- These are actual open immersions of the original tensor normalization charts. -/
theorem extendedClosedGaussNormalizationTensorChartInclusion_isOpenImmersion
    (s : Fin 4 ≃ Option (Fin 3)) :
    IsOpenImmersion (extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s) := by
  unfold extendedClosedGaussNormalizationTensorChartInclusion
  infer_instance

/-- The actual global point represented by the original canonical tensor normalization prime. -/
@[irreducible] noncomputable def extendedClosedGaussNormalizationTensorChartPoint
    (s : Fin 4 ≃ Option (Fin 3)) (q : PrimeSpectrum (normalizationRing (S₀ s ⊗[C₀] E))) :
    extendedClosedGaussNormalizationScheme H I E hH e :=
  let j : Spec (CommRingCat.of (normalizationRing (S₀ s ⊗[C₀] E))) ⟶
      extendedClosedGaussNormalizationScheme H I E hH e :=
    extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s
  j q

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The original tensor normalization prime localization is the actual
global stalk on the normalization formed after coefficient extension. -/
noncomputable def extendedClosedGaussNormalizationTensorChartStalkIso
    (s : Fin 4 ≃ Option (Fin 3)) (q : PrimeSpectrum (normalizationRing (S₀ s ⊗[C₀] E))) :
    (extendedClosedGaussNormalizationScheme H I E hH e).presheaf.stalk
      (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q) ≃+*
        Localization.AtPrime q.asIdeal := by
  let j : Spec (CommRingCat.of (normalizationRing (S₀ s ⊗[C₀] E))) ⟶
      extendedClosedGaussNormalizationScheme H I E hH e :=
    extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s
  let : IsOpenImmersion j :=
    extendedClosedGaussNormalizationTensorChartInclusion_isOpenImmersion H I E hH e s
  unfold extendedClosedGaussNormalizationTensorChartPoint
  exact schemeAffineOpenImmersionStalkIso (CommRingCat.of (normalizationRing (S₀ s ⊗[C₀] E))) j q

end DimensionFourDependence
