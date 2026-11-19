import DimensionFourDependence.ExtendedGaussNormalizationSourceDiagram
import DimensionFourDependence.ExtendedGaussNormalizationStalkMaps

/-! # Actual geometric source-stalk maps are the original tensor source maps

The actual global projection to the original projective source pulls
back every original projective section to its original source value in
the tensor-normalization prime localization. This identifies geometric
source pullback germs with the source functions of the local models.
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

/-- Every source-ratio chart function is represented by an actual
projective section on that same original coordinate open. -/
theorem projectiveAmbientSectionToSource_surjective
    {C F : Type u} [Field C] [Field F] [Algebra C F]
    (x : Fin 4 → F) (a : Fin 4) (ha : x a ≠ 0) :
    Function.Surjective (projectiveAmbientSectionToSource (C := C) x a ha) :=
  (homogeneousCoordinateChartToSource_surjective (C := C) x a ha).comp
    (Proj.basicOpenIsoAway (homogeneousSubmodule (Fin 4) C) (X a)
      (isHomogeneous_X (R := C) a) (by omega)).symm.commRingCatIsoToRingEquiv.surjective

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K) x₀ (s.symm none)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N₀" => normalizationRing T₀
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "jₑ" => extendedClosedGaussNormalizationTensorChartInclusion H I E hH e s
local notation "Uₖ" => Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X (s.symm none))

/-- The actual global source pullback germ of an original projective
section at the given original tensor-normalization prime. -/
@[irreducible] noncomputable def extendedClosedGaussNormalizationProjectiveSourceGerm
    (q : PrimeSpectrum N₀)
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K), Uₖ)) :
    (Nₑ).presheaf.stalk (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q) :=
  (Nₑ).presheaf.germ ((mₑ) ⁻¹ᵁ Uₖ)
    (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q)
    (extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q)
    ((mₑ).app Uₖ r)

/-- This germ is the pullback by the actual geometric source stalk
map, with its original projective section germ. -/
theorem extendedClosedGaussNormalizationProjectiveSourceGerm_stalkMap
    (q : PrimeSpectrum N₀)
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K), Uₖ)) :
    (mₑ).stalkMap (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q)
      ((AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)).presheaf.germ Uₖ
        ((mₑ) (extendedClosedGaussNormalizationTensorChartPoint H I E hH e s q))
        (extendedClosedGaussNormalizationTensorChartPoint_source_mem H I E hH e s q) r) =
      extendedClosedGaussNormalizationProjectiveSourceGerm H I E hH e s q r := by
  unfold extendedClosedGaussNormalizationProjectiveSourceGerm
  exact Scheme.Hom.germ_stalkMap_apply _ _ _ _ _

/-- The actual geometric source projection's stalk pullback has the
original source value in the original tensor-normalization localization. -/
theorem extendedClosedGaussNormalizationTensorChartStalkIso_projective_source_germ
    (q : PrimeSpectrum N₀)
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K), Uₖ)) :
    extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q
      (extendedClosedGaussNormalizationProjectiveSourceGerm H I E hH e s q r) =
      algebraMap N₀ (Localization.AtPrime q.asIdeal)
        (algebraMap T₀ N₀ (extendedClosedGaussProjectiveSourceSectionHom H I E s r)) := by
  let : IsOpenImmersion jₑ :=
    extendedClosedGaussNormalizationTensorChartInclusion_isOpenImmersion H I E hH e s
  let U : (AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)).affineOpens :=
    ⟨Uₖ, Proj.isAffineOpen_basicOpen _ _ (isHomogeneous_X (R := K) _) (by omega)⟩
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  let φ : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K), U.1) ⟶ CommRingCat.of N₀ :=
    CommRingCat.ofHom ((algebraMap T₀ N₀).comp (extendedClosedGaussProjectiveSourceSectionHom H I E s))
  have h := schemeAffineOpenImmersionStalkIso_pullback_germ
    (CommRingCat.of N₀) jₑ mₑ U φ
    (extendedClosedGaussNormalizationTensorChartInclusion_to_source H I E hH e s) q r
  unfold extendedClosedGaussNormalizationProjectiveSourceGerm
    extendedClosedGaussNormalizationTensorChartStalkIso
    extendedClosedGaussNormalizationTensorChartPoint
  convert! h using 1

/-- Geometric projective-source pullback agrees with the original
source-function germ already used by the local normalization models. -/
theorem extendedClosedGaussNormalizationProjectiveSourceGerm_eq_source_germ
    (q : PrimeSpectrum N₀)
    (r : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K), Uₖ)) :
    extendedClosedGaussNormalizationProjectiveSourceGerm H I E hH e s q r =
      extendedClosedGaussNormalizationSourceGerm H I E hH e s q
        (projectiveAmbientSectionToSource (C := K) x₀ (s.symm none)
          (source_rationalCoordinate_ne_zero _) r) := by
  apply (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e s q).injective
  have hnew := extendedClosedGaussNormalizationTensorChartStalkIso_projective_source_germ H I E hH e s q r
  have hold := extendedClosedGaussNormalizationTensorChartStalkIso_source_germ H I E hH e s q
    (projectiveAmbientSectionToSource (C := K) x₀ (s.symm none) (source_rationalCoordinate_ne_zero _) r)
  exact hnew.trans hold.symm

/-- Every original source-chart function has an actual projective
section whose geometric source pullback is its specified original local
model germ on the global normalization. -/
theorem extendedClosedGaussNormalizationSourceGerm_exists_projective_section
    (q : PrimeSpectrum N₀) (r : R₀) :
    ∃ u : Γ(AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K), Uₖ),
      projectiveAmbientSectionToSource (C := K) x₀ (s.symm none)
          (source_rationalCoordinate_ne_zero _) u = r ∧
        extendedClosedGaussNormalizationProjectiveSourceGerm H I E hH e s q u =
          extendedClosedGaussNormalizationSourceGerm H I E hH e s q r := by
  obtain ⟨u, hu⟩ := projectiveAmbientSectionToSource_surjective x₀ (s.symm none)
    (source_rationalCoordinate_ne_zero _) r
  refine ⟨u, hu, ?_⟩
  rw [extendedClosedGaussNormalizationProjectiveSourceGerm_eq_source_germ, hu]

end DimensionFourDependence
