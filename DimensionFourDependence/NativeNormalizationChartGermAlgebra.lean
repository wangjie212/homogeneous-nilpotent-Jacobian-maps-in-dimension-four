import DimensionFourDependence.ExtendedOwnFunctionFieldEquiv
import DimensionFourDependence.ExtendedNormalizedChartGerms
import DimensionFourDependence.NativeProjectiveResidueIdeal

/-! # The original normalization chart acts on the actual stalk over the same coefficients -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Compose an actual affine-section morphism with a specified
coordinate-ring isomorphism, retaining its literal geometric value. -/
noncomputable def commRingCatHomCompRingEquiv
    {R : Type u} [CommRing R] {S T : CommRingCat.{u}}
    (g : S ⟶ T) (b : R ≃+* S) : R →+* T := g.hom.comp b.toRingHom

/-- The composition is exactly the original geometric morphism
applied to the original coordinate value. -/
theorem commRingCatHomCompRingEquiv_apply
    {R : Type u} [CommRing R] {S T : CommRingCat.{u}}
    (g : S ⟶ T) (b : R ≃+* S) (r : R) :
    commRingCatHomCompRingEquiv g b r = g (b r) := rfl

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (a : Fin 4)

local notation "C₀" => closedGaussParameterField H I
local notation "s₀" => finSuccEquiv' a
local notation "T₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((s₀).symm none) ⊗[C₀] E
local notation "S₀" => normalizationRing (T₀)
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U₀" => extendedClosedGaussNormalizationChartOpen H I E hH e (s₀)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "z₀" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (s₀) q
local notation "ha₀" q:max => extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (s₀) q

local instance nativeNormalizationChartGermIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance nativeNormalizationChartGermDomain : IsDomain (T₀) :=
  original_tensor_pencil_chart_isDomain H I E (s₀)
local instance nativeNormalizationChartGermNonempty : Nonempty (U₀) :=
  extendedClosedGaussNormalizationChartOpen_nonempty H I E hH e (s₀)
noncomputable local instance nativeNormalizationChartGermFieldAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The original normalization ring acts by its actual regular
sections and actual germs at the specified tensor-chart prime. -/
noncomputable def nativeNormalizationChartGermHom (q : PrimeSpectrum (S₀)) :
    S₀ →+* (N).presheaf.stalk (z₀ q) :=
  commRingCatHomCompRingEquiv ((N).presheaf.germ (U₀) (z₀ q) (ha₀ q))
    (extendedClosedGaussNormalizedChartSectionEquiv H I E hH e (s₀)).symm

/-- The actual germ retains the original normalization element's
specified value in the native source function field. -/
theorem nativeNormalizationChartGermHom_value (q : PrimeSpectrum (S₀)) (r : S₀) :
    algebraMap ((N).presheaf.stalk (z₀ q)) (N).functionField
      (nativeNormalizationChartGermHom H I E hH e a q r) =
      extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv H I E hH e (s₀)
        (algebraMap (S₀) (FractionRing (T₀)) r) := by
  let b := extendedClosedGaussNormalizedChartSectionEquiv H I E hH e (s₀)
  let f := extendedClosedGaussNormalizedChartFunctionFieldEquiv H I E hH e (s₀)
  have hh := congrArg (algebraMap ((N).presheaf.stalk (z₀ q)) (N).functionField)
    (@commRingCatHomCompRingEquiv_apply (S₀) (inferInstance : CommRing (S₀))
      Γ(N, U₀) ((N).presheaf.stalk (z₀ q))
      ((N).presheaf.germ (U₀) (z₀ q) (ha₀ q)) b.symm r)
  apply hh.trans
  change algebraMap ((N).presheaf.stalk (z₀ q)) (N).functionField
    ((N).presheaf.germ (U₀) (z₀ q) (ha₀ q) (b.symm r)) = f _
  calc
    _ = (N).germToFunctionField (U₀) (b.symm r) :=
      Scheme.algebraMap_germ_eq_germToFunctionField N (ha₀ q) (b.symm r)
    _ = f (extendedClosedGaussNormalizedChartSectionValue H I E hH e (s₀) (b.symm r)) :=
      (extendedClosedGaussNormalizedChartFunctionFieldEquiv_section H I E hH e (s₀) (b.symm r)).symm
    _ = f (algebraMap (S₀) (FractionRing (T₀)) r) :=
      congrArg f (congrArg (algebraMap (S₀) (FractionRing (T₀))) (b.apply_symm_apply r))

/-- Every original normalized element has its canonical prime-local
value under the actual scheme stalk identification. -/
theorem nativeNormalizationChartGermHom_localization (q : PrimeSpectrum (S₀)) (r : S₀) :
    extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e (s₀) q
      (nativeNormalizationChartGermHom H I E hH e a q r) =
      algebraMap (S₀) (Localization.AtPrime q.asIdeal) r := by
  let b := extendedClosedGaussNormalizedChartSectionEquiv H I E hH e (s₀)
  have he := extendedClosedGaussNormalizationTensorChartStalkIso_regular_germ H I E hH e (s₀) q (b.symm r)
  have hh := congrArg (extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e (s₀) q)
    (@commRingCatHomCompRingEquiv_apply (S₀) (inferInstance : CommRing (S₀))
      Γ(N, U₀) ((N).presheaf.stalk (z₀ q))
      ((N).presheaf.germ (U₀) (z₀ q) (ha₀ q)) b.symm r)
  exact hh.trans (he.trans (congrArg (algebraMap (S₀) (Localization.AtPrime q.asIdeal)) (b.apply_symm_apply r)))

/-- The actual chart-stalk isomorphism is over the original extended
coefficient field, so its residue equivalence keeps the same constants. -/
noncomputable def nativeNormalizationChartStalkAlgEquiv (q : PrimeSpectrum (S₀)) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ q)
    (N).presheaf.stalk (z₀ q) ≃ₐ[E] Localization.AtPrime q.asIdeal := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ q)
  letI := extendedClosedGaussStalkCoefficientAlgebra_scalarTower H I E hH e (z₀ q)
  let β := extendedClosedGaussNormalizationTensorChartStalkIso H I E hH e (s₀) q
  refine { β with commutes' := ?_ }
  intro c
  let r : S₀ := algebraMap (T₀) (S₀) (algebraMap E (T₀) c)
  have hc : nativeNormalizationChartGermHom H I E hH e a q r =
      algebraMap E ((N).presheaf.stalk (z₀ q)) c := by
    apply IsFractionRing.injective ((N).presheaf.stalk (z₀ q)) (N).functionField
    rw [nativeNormalizationChartGermHom_value]
    dsimp only [r]
    rw [← IsScalarTower.algebraMap_apply (T₀) (S₀) (FractionRing (T₀)),
      ← IsScalarTower.algebraMap_apply E (T₀) (FractionRing (T₀)), AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply E ((N).presheaf.stalk (z₀ q)) (N).functionField]
  calc
    β (algebraMap E ((N).presheaf.stalk (z₀ q)) c) =
        β (nativeNormalizationChartGermHom H I E hH e a q r) := congrArg β hc.symm
    _ = algebraMap (S₀) (Localization.AtPrime q.asIdeal) r :=
      nativeNormalizationChartGermHom_localization H I E hH e a q r
    _ = algebraMap (T₀) (Localization.AtPrime q.asIdeal) (algebraMap E (T₀) c) :=
      (IsScalarTower.algebraMap_apply (T₀) (S₀) (Localization.AtPrime q.asIdeal) _).symm
    _ = algebraMap E (Localization.AtPrime q.asIdeal) c :=
      (IsScalarTower.algebraMap_apply E (T₀) (Localization.AtPrime q.asIdeal) c).symm

/-- The same actual normalized chart action sends the original
affine tensor coordinates to their actual original projective-coordinate germs. -/
theorem nativeNormalizationChartGermHom_coordinate (q : PrimeSpectrum (S₀)) (i : Fin 3) :
    nativeNormalizationChartGermHom H I E hH e a q
      (algebraMap (T₀) (S₀) (originalTensorPencilCoordinate H I E (s₀) i)) =
      nativeProjectiveCoordinateGerm H I E hH e (z₀ q) a (ha₀ q) ((s₀).symm (some i)) := by
  apply IsFractionRing.injective ((N).presheaf.stalk (z₀ q)) (N).functionField
  rw [nativeNormalizationChartGermHom_value,
    ← IsScalarTower.algebraMap_apply (T₀) (S₀) (FractionRing (T₀)),
    extendedClosedGaussNormalizedChartFunctionFieldAlgEquiv_coordinate,
    nativeProjectiveCoordinateGerm_value, finSuccEquiv'_symm_none]

end DimensionFourDependence
