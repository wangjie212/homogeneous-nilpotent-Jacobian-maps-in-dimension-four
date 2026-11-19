import DimensionFourDependence.ActualNormalPlaneDivisorPoles
import DimensionFourDependence.ExtendedNonunitSectionDivisor

/-! # Every actual normalization-chart point supplies its canonical prime -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "T" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)

/-- Every point in the actual normalized chart is represented by
a prime of its original canonical normalization ring, preserving the
point itself and its intrinsic codimension. -/
theorem actual_normalization_chart_point_constructs_canonical_prime
    (a : Fin 4) (z : N) (hz : z ∈ V a) :
    ∃ q : PrimeSpectrum (normalizationRing (T a)),
      extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q = z ∧
      q.asIdeal.height = Order.coheight z := by
  let b := extendedClosedGaussNormalizationTensorChartIso H I E hH e (finSuccEquiv' a)
  let q : PrimeSpectrum (normalizationRing (T a)) := b.hom ⟨z, hz⟩
  have hq : extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q = z := by
    unfold extendedClosedGaussNormalizationTensorChartPoint
      extendedClosedGaussNormalizationTensorChartInclusion
    change (b.inv (b.hom ⟨z, hz⟩)).val = z
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  refine ⟨q, hq, ?_⟩
  rw [← hq]
  exact (extendedClosedGaussNormalizationTensorChartPoint_coheight_eq_height
    H I E hH e (finSuccEquiv' a) q).symm

variable (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E

local instance actualNormalizedChartPointPrimesIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance actualNormalizedChartPointPrimesAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable [Module.Finite (closedGaussParameterField H I) E]

/-- Every intrinsic height-one normal-plane point on the actual
normalization is a pole of the exact scaled-plane quotient. A canonical
chart prime and its source-divisor image are constructed internally. -/
theorem actual_normal_plane_height_one_point_scaled_quotient_nonregular
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (s n : Fin 4 → E) (hs : s (Fin.last 3) ≠ 0) (hnlast : n (Fin.last 3) = 0)
    (hn : aeval (w) ((O) n) ≠ 0) (hL0 : aeval (w) (L₀) ≠ 0) (c : E)
    (hpower : aeval (w) ((O) s) = algebraMap E (N).functionField c * (aeval (w) (L₀)) ^ d)
    (z : N) (hzheight : Order.coheight z = 1) (a : Fin 4) (hz : z ∈ V a)
    (hvan : extendedClosedGaussPolynomialCoefficientGerm H I E hH e (L₀) z a hz ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk z)) :
    ¬ IsLocalization.IsInteger ((N).presheaf.stalk z)
      (aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d) := by
  obtain ⟨q, hqz, hqheight⟩ := actual_normalization_chart_point_constructs_canonical_prime
    H I E hH e a z hz
  subst z
  exact actual_normal_plane_divisor_scaled_quotient_nonregular H I E hH e hd hind hGauss
    hvertex s n hs hnlast hn hL0 c hpower a q
    (hqheight.trans hzheight) hvan

end DimensionFourDependence
