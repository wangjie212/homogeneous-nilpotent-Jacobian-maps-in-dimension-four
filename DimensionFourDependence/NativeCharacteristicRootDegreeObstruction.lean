import DimensionFourDependence.NativeCharacteristicRootContainment
import DimensionFourDependence.NativeDivisorSourceIdealTransport
import DimensionFourDependence.ChosenCharacteristicOriginalIdeal
import DimensionFourDependence.CharacteristicImageDegreeLowerBound

/-! # The actual root divisor contradicts the characteristic image degree -/

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

local instance nativeCharacteristicRootDegreeObstructionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeCharacteristicRootDegreeObstructionAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

local notation "κ₀" a:max q:max => IsLocalRing.ResidueField (A₀ a q)
local notation "v₀" a:max q:max => fun i => IsLocalRing.residue (A₀ a q)
  (nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q) i)
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E

variable [IsAlgClosed K]
  (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "e₀" => actualGaussRulingParameterChoice H I hH (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss
local notation "v" => gaussParameterNormal H I (e₀)
local notation "P₀" r:max => pencilCoefficientCurveField (E := E)
  (nativeCharacteristicPencilValue H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r)

/-- The positive generic degree bound for this specified native root's
own relatively closed pencil coefficient field and original coordinates. -/
noncomputable def NativeCharacteristicPencilPositiveDegreeTwo (r : (N).functionField) : Prop :=
  ∃ D : ℕ, D ≤ 2 ∧ HasCurveHilbertDegree
    (projectiveFieldPointIdeal (E := P₀ r) (w)).toIdeal D

/-- The constructed branch inclusion contracts to the same fixed
original source curve, contradicting the nonplanar characteristic's
Hilbert growth when that source curve has degree at most two. -/
theorem actual_proportional_root_divisor_excluded_by_characteristic_degree
    [Module.Finite C₀ E]
    (S cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval (w) ((O) S))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hz : Order.coheight (z₀ a q) = 1)
    (hvan : (N).presheaf.germ (U₀ a) (z₀ a q) (ha₀ a q)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussOutputLinearRootSection H I E hH e S r
          (Nat.lt_trans Nat.zero_lt_one hd) hroot) a) ∈
      IsLocalRing.maximalIdeal (A₀ a q))
    (hres : NativeCharacteristicPencilCoefficientResidueAlgebraic H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r (z₀ a q) hz)
    (hdegree : NativeCharacteristicPencilDivisorPositiveDegreeTwo H I E hH e hd hind hGauss r a q hz)
    (hcompare : NativeCharacteristicBoundaryPointIdealComparison H I E hH e hd hind hGauss r)
    (bR : Fin 4 → RatFunc K) (hbR0 : bR ≠ 0)
    (hbRC : bR ∈ normalCharacteristicSubspace (rationalParameterDerivative K) (v))
    (hplane : ∀ c : Fin 4 → K,
      (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ bR = 0 → c = 0)
 : False := by
  have hfactorCopy := hfactor
  obtain ⟨V, W, hLI, _hV, _hWr, hW, _hspan, _hNW, _hcoord⟩ := hfactorCopy
  have hW0 : W ≠ 0 := by simpa using hLI.ne_zero (1 : Fin 2)
  have hinc := actual_characteristic_root_divisor_source_ideal_le_characteristic
    H I E hH e hd hind hGauss S cN r hr hroot hfactor a q hq hvan hcompare W hW0 hW
  have hincK := native_tensor_divisor_original_source_ideal_le_of_residue_ideal
    H I E hH e a q W hinc
  obtain ⟨D, hD2, hD⟩ := actual_characteristic_root_divisor_fixed_source_degree_at_most_two
    H I E hH e hd hind hGauss S cN r hroot hfactor a q hq hz hvan hres hdegree
  letI : Algebra K E := (ι).toAlgebra
  letI : SMul K E := (ι).toAlgebra.toSMul
  have hEq := chosen_extended_characteristic_original_point_ideal_eq H I E hH
    (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss bR hbR0 hbRC W hW0 hW
  have hcontain : (projectiveFieldPointIdeal (E := K) (x₀ a q)).toIdeal ≤
      (projectiveFieldPointIdeal (E := K) bR).toIdeal := hincK.trans hEq.le
  exact nonplanar_rational_curve_not_contained_in_degree_two_curve
    bR hbR0 hplane _ hD2 hD hcontain

/-- The generic degree-two bound constructs the actual root divisor,
its algebraic coefficient residue and positive specialized degree. The
characteristic obstruction therefore needs no supplied divisor. -/
theorem actual_characteristic_degree_two_pencil_excluded_by_boundary_comparison
    [Module.Finite C₀ E]
    (S cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval (w) ((O) S))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r)
    (hcompare : NativeCharacteristicBoundaryPointIdealComparison H I E hH e hd hind hGauss r)
    (bR : Fin 4 → RatFunc K) (hbR0 : bR ≠ 0)
    (hbRC : bR ∈ normalCharacteristicSubspace (rationalParameterDerivative K) (v))
    (hplane : ∀ c : Fin 4 → K,
      (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ bR = 0 → c = 0)
    (hgeneric : NativeCharacteristicPencilPositiveDegreeTwo H I E hH e hd hind hGauss r) : False := by
  obtain ⟨a, q, hq, hz, hvan⟩ := actual_native_nonzero_root_section_has_zero_divisor
    H I E hH e hGauss (Nat.lt_trans Nat.zero_lt_one hd) S r hr hroot
  have hres := actual_characteristic_pencil_zero_coefficient_residue_isAlgebraic
    H I E hH e hd hind hGauss S cN r hr hroot hfactor a q hq hvan
  obtain ⟨D, hD2, hD⟩ := hgeneric
  obtain ⟨D', hle, hD'⟩ := actual_characteristic_pencil_divisor_curve_degree_exists
    H I E hH e (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss r a q hq hz hres hD
  have hdegree : NativeCharacteristicPencilDivisorPositiveDegreeTwo H I E hH e hd hind hGauss r a q hz :=
    ⟨D', hle.trans hD2, hD'⟩
  exact actual_proportional_root_divisor_excluded_by_characteristic_degree
    H I E hH e hd hind hGauss S cN r hr hroot hfactor a q hq hz hvan hres hdegree
      hcompare bR hbR0 hbRC hplane

end DimensionFourDependence
