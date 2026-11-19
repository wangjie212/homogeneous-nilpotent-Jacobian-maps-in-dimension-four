import DimensionFourDependence.CharacteristicRootOriginalBoundary
import DimensionFourDependence.NativeSpecializationPointRelations

/-! # Root-divisor branch containment from its original boundary point equations -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.gradedAlgebra
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

local instance nativeCharacteristicRootContainmentIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeCharacteristicRootContainmentAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "v₀" a:max q:max => fun i => IsLocalRing.residue (A₀ a q)
  (nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q) i)
local notation "U" b:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' b)
local notation "x₀" z:max b:max hb:max => fun i => IsLocalRing.residue ((N).presheaf.stalk z)
  (nativeProjectiveCoordinateGerm H I E hH e z b hb i)

/-- The exact whole equation comparison needed on each constructed
original full-fiber boundary. The proportional-power original graph
calculation supplies this property, separately from the native chart. -/
noncomputable def NativeCharacteristicBoundaryPointIdealComparison (r : (N).functionField) : Prop :=
  ∀ (z : N) (b : Fin 4) (hb : z ∈ U b),
    NativeCharacteristicOriginalFiberBoundaryAtPoint H I E hH e hd hind hGauss r z b hb →
    ∀ (W : Fin 4 → E), W ≠ 0 →
      W ∈ extendedClosedGaussChosenCharacteristicSubspace H I E hH
        (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss →
      letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
      (projectiveFieldPointIdeal (E := E) (x₀ z b hb)).toIdeal =
        (projectiveFieldPointIdeal (E := E) W).toIdeal

/-- The proper root-divisor specialization constructs the point at
which the complete characteristic equation comparison is applied. -/
theorem actual_characteristic_root_divisor_source_ideal_le_characteristic
    [Module.Finite C₀ E]
    (S cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval (w) ((O) S))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hvan : (N).presheaf.germ (U₀ a) (z₀ a q) (ha₀ a q)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e
        (extendedClosedGaussOutputLinearRootSection H I E hH e S r
          (Nat.lt_trans Nat.zero_lt_one hd) hroot) a) ∈
      IsLocalRing.maximalIdeal (A₀ a q))
    (hcompare : NativeCharacteristicBoundaryPointIdealComparison H I E hH e hd hind hGauss r)
    (W : Fin 4 → E) (hW0 : W ≠ 0)
    (hW : W ∈ extendedClosedGaussChosenCharacteristicSubspace H I E hH
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
    (projectiveFieldPointIdeal (E := E) (v₀ a q)).toIdeal ≤
      (projectiveFieldPointIdeal (E := E) W).toIdeal := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
  obtain ⟨z, hxz, _hne, b, hb, hboundary⟩ :=
    actual_characteristic_root_divisor_constructs_original_full_output_boundary
      H I E hH e hd hind hGauss S cN r hr hroot hfactor a q hq hvan
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e z
  have hEq := hcompare z b hb hboundary W hW0 hW
  exact (native_projective_coordinate_residue_ideal_le_of_specializes
    H I E hH e (z₀ a q) z hxz a b (ha₀ a q) hb).trans hEq.le

end DimensionFourDependence
