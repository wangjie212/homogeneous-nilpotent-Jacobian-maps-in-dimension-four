import DimensionFourDependence.NativeDivisorFixedCurveDegreeTwo
import DimensionFourDependence.ProjectivePointCoefficientRestriction

/-! # The actual branch inclusion retains the original fixed-source equations -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.gradedAlgebra
attribute [local instance] tensorPencilResidueGenerationNormalizationRing
  tensorPencilResidueGenerationResidueField tensorPencilResidueGenerationCoordinateAlgebra
  tensorPencilResidueGenerationCoordinateSMul tensorPencilResidueGenerationSourceTower
  tensorPencilResidueGenerationExtendedAlgebra tensorPencilResidueGenerationClosedAlgebra
  tensorPencilResidueGenerationClosedSMul tensorPencilResidueGenerationExtendedSMul
  tensorPencilResidueGenerationClosedTower tensorPencilResidueGenerationOriginalSMul
  tensorPencilResidueGenerationOriginalTower
attribute [local instance 2000] originalTensorPencilResidueOriginalAlgebra
  tensorPencilResiduePointAddCommMonoid tensorPencilResiduePointSemiring
  tensorPencilResiduePointOriginalModule tensorPencilResiduePointOriginalMulAction

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "F₀" a:max q:max => FractionRing (normalizationRing (T₀ a) ⧸ (q).asIdeal)
local notation "y₀" a:max q:max => originalTensorPencilResidueCoordinate H I E (finSuccEquiv' a) (q).asIdeal
local notation "x₀" a:max q:max => fun i : Fin 4 => (finSuccEquiv' a i).elim 1 (y₀ a q)
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "z₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "ha₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q
local notation "U₀" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "A₀" a:max q:max => (N).presheaf.stalk (z₀ a q)

local instance nativeDivisorSourceIdealTransportIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeDivisorSourceIdealTransportAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

local notation "κ₀" a:max q:max => IsLocalRing.ResidueField (A₀ a q)
local notation "v₀" a:max q:max => fun i => IsLocalRing.residue (A₀ a q)
  (nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q) i)
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E

/-- The entire projective ideal agrees under the actual four-coordinate
residue realization, over the specified extended Gauss constants. -/
theorem native_tensor_divisor_restored_source_ideal_eq_residue_ideal
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
    (projectiveFieldPointIdeal (E := E) (x₀ a q)).toIdeal =
      (projectiveFieldPointIdeal (E := E) (v₀ a q)).toIdeal := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
  let φ := nativeTensorDivisorResidueAlgEquiv H I E hH e a q
  have hv : (fun i => φ ((v₀ a q) i)) = (x₀ a q) :=
    funext (nativeTensorDivisorResidueAlgEquiv_projective_coordinate H I E hH e a q)
  rw [← hv]
  exact projectiveFieldPointIdeal_algHom (v₀ a q) φ.toAlgHom

/-- A native equation inclusion contracts to the complete ideal of the
same fixed source curve over the original ground field. The original
quotient-fraction coordinate action is retained in the conclusion. -/
theorem native_tensor_divisor_original_source_ideal_le_of_residue_ideal
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (W : Fin 4 → E)
    (hinc : letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
      (projectiveFieldPointIdeal (E := E) (v₀ a q)).toIdeal ≤
        (projectiveFieldPointIdeal (E := E) W).toIdeal) :
    letI : Algebra K E := (ι).toAlgebra
    (projectiveFieldPointIdeal (E := K) (x₀ a q)).toIdeal ≤
      (projectiveFieldPointIdeal (E := K) W).toIdeal := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
  letI : Algebra E (F₀ a q) := normalizationPrimeResidueCoefficientAlgebra (E := E) q.asIdeal
  letI : SMul E (F₀ a q) :=
    (normalizationPrimeResidueCoefficientAlgebra (E := E) q.asIdeal).toSMul
  letI : Algebra K (F₀ a q) :=
    originalTensorPencilResidueOriginalAlgebra H I E (finSuccEquiv' a) q.asIdeal
  letI : SMul K (F₀ a q) :=
    (originalTensorPencilResidueOriginalAlgebra H I E (finSuccEquiv' a) q.asIdeal).toSMul
  letI : Algebra K E := (ι).toAlgebra
  letI : SMul K E := (ι).toAlgebra.toSMul
  letI : IsScalarTower K E (F₀ a q) := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap C₀ (F₀ a q) (algebraMap K C₀ c) =
      algebraMap E (F₀ a q) ((ι) c)
    exact IsScalarTower.algebraMap_apply C₀ E (F₀ a q) _)
  have hE := (native_tensor_divisor_restored_source_ideal_eq_residue_ideal
    H I E hH e a q).le.trans hinc
  exact projectiveFieldPointIdeal_le_of_extended_coefficients (E := E) (x₀ a q) W hE

end DimensionFourDependence
