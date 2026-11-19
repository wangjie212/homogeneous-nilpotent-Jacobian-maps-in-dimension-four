import DimensionFourDependence.AffineChartStalkNaturality
import DimensionFourDependence.ExtendedGaussNormalizationMorphism
import DimensionFourDependence.ExtendedGaussSourceNormalization

/-! # Actual global normalization stalks retain the pencil section pullback

The global normalization morphism pulls back actual pencil sections.
Its stalk identification with the original tensor-normalization prime
localization preserves those section values and the source functions
represented in the actual tensor coordinate chart.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

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
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N₀" => normalizationRing T₀
local notation "Qₑ" => extendedClosedGaussPencilScheme H I E hH e
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "Uₑ" => extendedClosedGaussPencilChartOpen H I E hH e s
local notation "nₑ" => extendedClosedGaussNormalizationSchemeMap H I E hH e
local notation "jₑ" => extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s

/-- The actual global germ of a pencil section pulled back by the
global normalization morphism, at the given original tensor-chart prime. -/
@[irreducible] noncomputable def extendedClosedGaussNormalizationPencilGerm
    (q : PrimeSpectrum N₀) (r : Γ(Qₑ, Uₑ)) :
    (Nₑ).presheaf.stalk (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q) := by
  let φ : Γ(Qₑ, Uₑ) ⟶ CommRingCat.of N₀ := CommRingCat.ofHom
    ((algebraMap T₀ N₀).comp (extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s).toRingHom)
  have hd := extendedClosedGaussNormalizationTensorChartInclusion_to_base H I E hH e s
  have hq : jₑ q ∈ nₑ ⁻¹ᵁ Uₑ := affineSourceDiagram_mem
    (CommRingCat.of N₀) ⟨Uₑ, extendedClosedGaussPencilChartOpen_isAffineOpen H I E hH e s⟩
    φ (jₑ ≫ nₑ) hd q
  unfold extendedClosedGaussNormalizationTensorChartPoint
  exact (Nₑ).presheaf.germ (nₑ ⁻¹ᵁ Uₑ) (jₑ q) hq ((nₑ).app Uₑ r)

/-- The actual global normalization pullback of every pencil section
is its original coordinate value in the original prime localization. -/
theorem extendedClosedGaussNormalizationTensorChartStalkIso_pencil_germ
    (q : PrimeSpectrum N₀) (r : Γ(Qₑ, Uₑ)) :
    extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q
      (extendedClosedGaussNormalizationPencilGerm H I E hH e s q r) =
      algebraMap N₀ (Localization.AtPrime q.asIdeal)
        (algebraMap T₀ N₀ (extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s r)) := by
  let : IsOpenImmersion jₑ :=
    extendedClosedGaussNormalizationTensorChartInclusion_isOpenImmersion H I E hH e s
  unfold extendedClosedGaussNormalizationPencilGerm
    extendedClosedGaussNormalizationTensorChartStalkIso
  exact schemeAffineOpenImmersionStalkIso_pullback_germ (CommRingCat.of N₀) jₑ nₑ
    ⟨Uₑ, extendedClosedGaussPencilChartOpen_isAffineOpen H I E hH e s⟩
    (CommRingCat.ofHom ((algebraMap T₀ N₀).comp
      (extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s).toRingHom))
    (extendedClosedGaussNormalizationTensorChartInclusion_to_base H I E hH e s) q r

/-- The original source-chart function, represented in the actual
pencil sections, is pulled back through the actual global normalization. -/
noncomputable def extendedClosedGaussNormalizationSourceGerm
    (q : PrimeSpectrum N₀) (r : R₀) :
    (Nₑ).presheaf.stalk (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q) :=
  extendedClosedGaussNormalizationPencilGerm H I E hH e s q
    ((extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s).symm
      (extendedClosedGaussTensorSourceHom H I E s r))

/-- The global stalk comparison retains the specified original source
function through the actual pencil-section pullback. -/
theorem extendedClosedGaussNormalizationTensorChartStalkIso_source_germ
    (q : PrimeSpectrum N₀) (r : R₀) :
    extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q
      (extendedClosedGaussNormalizationSourceGerm H I E hH e s q r) =
      algebraMap N₀ (Localization.AtPrime q.asIdeal)
        (extendedClosedGaussTensorNormalizationSourceHom H I E s r) := by
  unfold extendedClosedGaussNormalizationSourceGerm
  have h := extendedClosedGaussNormalizationTensorChartStalkIso_pencil_germ H I E hH e s q
    ((extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s).symm
      (extendedClosedGaussTensorSourceHom H I E s r))
  exact h.trans (congrArg (algebraMap N₀ (Localization.AtPrime q.asIdeal))
    (congrArg (algebraMap T₀ N₀)
      ((extendedClosedGaussPencilTensorChartSectionEquiv H I E hH e s).apply_symm_apply _)))

end DimensionFourDependence
