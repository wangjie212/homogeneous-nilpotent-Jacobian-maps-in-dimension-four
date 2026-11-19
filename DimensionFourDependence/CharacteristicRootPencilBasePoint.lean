import DimensionFourDependence.NativeDivisorHyperplaneIntersection
import DimensionFourDependence.NativeRootSectionSpecialization
import DimensionFourDependence.CharacteristicPencilNoCommonDivisor
import DimensionFourDependence.CharacteristicRootZeroDivisor

/-! # Every actual characteristic-root divisor constructs a common zero of the pencil -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

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
  [Module.Finite (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 1 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss 0
local notation "z₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "ha₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q
local notation "ρ₀" c:max r:max hroot:max => extendedClosedGaussOutputLinearRootSection H I E hH e
  c r (Nat.lt_trans Nat.zero_lt_one hd) hroot
local notation "L₀" => extendedClosedGaussInputLinearSection H I E hH e (ν₀)

local instance characteristicRootPencilBasePointIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicRootPencilBasePointAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Each actual root-zero divisor has a proper specialization on
that same branch where both actual pencil sections vanish. The
intersection point and its original coordinate chart are constructed. -/
theorem actual_characteristic_root_divisor_constructs_pencil_base_point
    (cS cN : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval (w) ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (hzero : (N).presheaf.germ (U a) (z₀ a q) (ha₀ a q)
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (ρ₀ cS r hroot) a) ∈
        IsLocalRing.maximalIdeal ((N).presheaf.stalk (z₀ a q))) :
    ∃ z : N, (z₀ a q) ⤳ z ∧ (z₀ a q) ≠ z ∧
      ∃ (b : Fin 4) (hb : z ∈ U b),
        (N).presheaf.germ (U b) z hb
          (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (ρ₀ cS r hroot) b) ∈
            IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ∧
        (N).presheaf.germ (U b) z hb
          (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (L₀) b) ∈
            IsLocalRing.maximalIdeal ((N).presheaf.stalk z) := by
  have hnot := characteristic_root_and_tangent_plane_have_no_common_divisor
    H I E hH e hd hind hGauss cS cN r hroot hfactor a q hq hzero
  have hNoLt : linearFormPolynomial (ν₀) ∉ ((f) (z₀ a q)).asHomogeneousIdeal := by
    intro hL
    exact hnot ((native_input_linear_section_zero_iff_source_equation
      H I E hH e (ν₀) (z₀ a q) a (ha₀ a q)).mpr hL)
  obtain ⟨z, hxz, hLz⟩ := actual_native_divisor_branch_meets_hyperplane
    H I E hH e hGauss a q hq (linearFormPolynomial (ν₀))
    (extendedClosedGaussInputLinearPolynomial_homogeneous E (ν₀))
  obtain ⟨b, hb⟩ := mem_iSup.mp
    ((extendedClosedGaussNormalizationChartOpen_iSup H I E hH e).ge
      (show z ∈ (⊤ : (N).Opens) from trivial))
  refine ⟨z, hxz, ?_, b, hb, ?_, ?_⟩
  · intro he
    exact hNoLt ((congrArg (fun y : N => linearFormPolynomial (ν₀) ∈ ((f) y).asHomogeneousIdeal) he).mpr hLz)
  · exact native_output_linear_root_zero_specializes H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) cS r hroot (z₀ a q) z hxz a (ha₀ a q) b hb hzero
  · exact (native_input_linear_section_zero_iff_source_equation H I E hH e (ν₀) z b hb).mpr hLz

/-- A nonzero characteristic root constructs an actual base point
of its own pencil with the chosen tangent-plane section. No divisor,
intersection point, source chart or local vanishing data are supplied. -/
theorem actual_characteristic_root_constructs_pencil_base_point
    (cS cN : Fin 4 → E) (r : (N).functionField) (hr : r ≠ 0)
    (hroot : r ^ d = aeval (w) ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r) :
    ∃ (z : N) (b : Fin 4) (hb : z ∈ U b),
      (N).presheaf.germ (U b) z hb
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (ρ₀ cS r hroot) b) ∈
          IsLocalRing.maximalIdeal ((N).presheaf.stalk z) ∧
      (N).presheaf.germ (U b) z hb
        (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (L₀) b) ∈
          IsLocalRing.maximalIdeal ((N).presheaf.stalk z) := by
  obtain ⟨a, q, hq, _hz, hzero⟩ := actual_native_nonzero_root_section_has_zero_divisor
    H I E hH e hGauss (Nat.lt_trans Nat.zero_lt_one hd) cS r hr hroot
  obtain ⟨z, _hxz, _hne, b, hb, hρ, hL⟩ :=
    actual_characteristic_root_divisor_constructs_pencil_base_point
      H I E hH e hd hind hGauss cS cN r hroot hfactor a q hq hzero
  exact ⟨z, b, hb, hρ, hL⟩

end DimensionFourDependence
