import DimensionFourDependence.NativeNormalizationChartGermAlgebra
import DimensionFourDependence.TensorPencilResidueDimensionExact
import DimensionFourDependence.NormalizationDivisorResidueParameter

/-! # Every actual native divisor has a transcendental original coordinate residue -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- A local algebra isomorphism preserves transcendence of a
specified original residue coordinate, with its exact local value. -/
theorem transcendental_residue_of_local_algEquiv
    {E A B : Type*} [Field E] [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra E A] [Algebra E B]
    (β : A ≃ₐ[E] B) (x : A) (y : B) (hxy : β x = y)
    (hy : Transcendental E (IsLocalRing.residue B y)) :
    Transcendental E (IsLocalRing.residue A x) := by
  let γ := IsLocalRing.ResidueField.mapAlgEquiv (R := E) β
  intro hx
  have he := (isAlgebraic_algHom_iff γ.toAlgHom γ.injective).mpr hx
  have hv : γ (IsLocalRing.residue A x) = IsLocalRing.residue B y :=
    (IsLocalRing.ResidueField.mapAlgEquiv_residue (R := E) β x).trans
      (congrArg (IsLocalRing.residue B) hxy)
  exact hy (hv ▸ he)

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "z₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "ha₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q

local instance nativeDivisorResidueTranscendenceIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance nativeDivisorResidueTranscendenceDomain (a : Fin 4) : IsDomain (T₀ a) :=
  original_tensor_pencil_chart_isDomain H I E (finSuccEquiv' a)

/-- At every actual original tensor-normalization divisor, one
actual original source-coordinate germ has transcendental residue
over the same extended Gauss constants. The scalar-compatible native
stalk identification and the nonclosed source coordinate are constructed. -/
theorem actual_native_divisor_has_transcendental_original_coordinate_residue
    (hGauss : gaussImageDimension H I = 1)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
    ∃ i : Fin 4, Transcendental E (IsLocalRing.residue ((N).presheaf.stalk (z₀ a q))
      (nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q) i)) := by
  let A := T₀ a
  let S := normalizationRing A
  let B := Localization.AtPrime q.asIdeal
  let φ := originalTensorPencilCoordinateEquiv H I E (finSuccEquiv' a)
  letI : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  letI : Algebra.FiniteType C₀ (closedGaussPencilChartAlgebra H I (finSuccEquiv' a)) :=
    closedGaussPencilChartAlgebra_finiteType H I (finSuccEquiv' a)
  letI : Algebra.FiniteType E A := (inferInstance : Algebra.FiniteType E
    (E ⊗[C₀] closedGaussPencilChartAlgebra H I (finSuccEquiv' a))).equiv φ.symm
  obtain ⟨i, hi⟩ := canonical_normalization_height_one_has_transcendental_original_coordinate
    (E := E) (originalTensorPencilCoordinate H I E (finSuccEquiv' a))
    (originalTensorPencilCoordinate_adjoin H I E (finSuccEquiv' a))
    (original_tensor_pencil_trdeg_two H I E hH e hGauss (finSuccEquiv' a)).ge q.asIdeal hq
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
  let β := nativeNormalizationChartStalkAlgEquiv H I E hH e a q
  let x := nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q)
    ((finSuccEquiv' a).symm (some i))
  refine ⟨(finSuccEquiv' a).symm (some i), ?_⟩
  apply transcendental_residue_of_local_algEquiv β x
    (algebraMap A B (originalTensorPencilCoordinate H I E (finSuccEquiv' a) i)) ?_ hi
  calc
    β x = β (nativeNormalizationChartGermHom H I E hH e a q
      (algebraMap A S (originalTensorPencilCoordinate H I E (finSuccEquiv' a) i))) :=
        congrArg β (nativeNormalizationChartGermHom_coordinate H I E hH e a q i).symm
    _ = algebraMap S B (algebraMap A S (originalTensorPencilCoordinate H I E (finSuccEquiv' a) i)) :=
      nativeNormalizationChartGermHom_localization H I E hH e a q _
    _ = algebraMap A B (originalTensorPencilCoordinate H I E (finSuccEquiv' a) i) :=
      (IsScalarTower.algebraMap_apply A S B _).symm

end DimensionFourDependence
