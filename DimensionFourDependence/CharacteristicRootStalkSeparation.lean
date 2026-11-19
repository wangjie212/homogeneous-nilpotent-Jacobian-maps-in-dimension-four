import DimensionFourDependence.CharacteristicPencilNoCommonDivisor
import DimensionFourDependence.ActualNormalizedChartPointPrimes
import DimensionFourDependence.AffineStalkPrimeRegularity

/-! # The actual characteristic pencil has no common height-one component in any native stalk -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

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

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "U" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH
  (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss 0
local notation "ρ₀" c:max r:max hroot:max => extendedClosedGaussOutputLinearRootSection H I E hH e
  c r (Nat.lt_trans Nat.zero_lt_one hd) hroot
local notation "L₀" => extendedClosedGaussInputLinearSection H I E hH e (ν₀)

local instance characteristicRootStalkSeparationIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicRootStalkSeparationAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Each height-one prime in an actual native stalk on the chosen
hyperplane avoids the root coefficient. The corresponding original
normalization point and its canonical chart prime are constructed. -/
theorem characteristic_root_avoids_tangent_plane_height_one_stalk_prime
    (cS cN : Fin 4 → E) (r : (N).functionField)
    (hroot : r ^ d = aeval (w) ((O) cS))
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e
      (Nat.lt_trans Nat.zero_lt_one hd) hind hGauss cN r)
    (z : N) (a : Fin 4) (hz : z ∈ U a)
    (Q : PrimeSpectrum ((N).presheaf.stalk z)) (hQ : Q.asIdeal.height = 1)
    (hL : (N).presheaf.germ (U a) z hz
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (L₀) a) ∈ Q.asIdeal) :
    (N).presheaf.germ (U a) z hz
      (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (ρ₀ cS r hroot) a) ∉ Q.asIdeal := by
  intro hρ
  obtain ⟨y, hy, hyheight, hsection, _hregular⟩ :=
    affine_stalk_prime_constructs_point_with_same_regular_fractions (U a)
      (extendedClosedGaussNormalizationChartOpen_isAffineOpen H I E hH e (finSuccEquiv' a)) z hz Q
  have hρy := (hsection
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (ρ₀ cS r hroot) a)).mp hρ
  have hLy := (hsection
    (extendedClosedGaussHyperplaneGlobalCoefficient H I E hH e (L₀) a)).mp hL
  obtain ⟨q, hqy, hqheight⟩ := actual_normalization_chart_point_constructs_canonical_prime
    H I E hH e a y hy
  subst y
  exact (characteristic_root_and_tangent_plane_have_no_common_divisor H I E hH e hd hind hGauss
    cS cN r hroot hfactor a q (hqheight.trans (hyheight.trans hQ)) hρy) hLy

end DimensionFourDependence
