import DimensionFourDependence.ActualNormalizedChartPointPrimes
import DimensionFourDependence.AffineStalkPrimeRegularity
import DimensionFourDependence.ScaledPlaneLocalHeightOneBranches

/-! # Every denominator branch in the actual normalized vertex stalk is a pole -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

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
    (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "germ" P:max z:max a:max hz:max =>
  extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z a hz

local instance actualVertexStalkDenominatorPolesIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance actualVertexStalkDenominatorPolesAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable [Module.Finite (closedGaussParameterField H I) E]

/-- Every height-one prime of the actual stalk containing the normal
coefficient is a pole of the exact original scaled-plane quotient. The
affine-chart point and its source divisor are constructed from that prime. -/
theorem actual_stalk_denominator_height_one_prime_scaled_quotient_pole
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (s n : Fin 4 → E) (hs : s (Fin.last 3) ≠ 0) (hnlast : n (Fin.last 3) = 0)
    (hn : aeval (w) ((O) n) ≠ 0) (hL0 : aeval (w) (L₀) ≠ 0) (c : E)
    (hpower : aeval (w) ((O) s) = algebraMap E (N).functionField c * (aeval (w) (L₀)) ^ d)
    (z : N) (a : Fin 4) (hz : z ∈ V a)
    (Q : PrimeSpectrum ((N).presheaf.stalk z)) (hQ : Q.asIdeal.height = 1)
    (hvan : germ (L₀) z a hz ∈ Q.asIdeal) :
    aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d ∉
      fractionPrimeLocalAlgebra ((N).presheaf.stalk z) Q.asIdeal := by
  obtain ⟨y, hy, hyheight, hsection, hregular⟩ :=
    affine_stalk_prime_constructs_point_with_same_regular_fractions (V a)
      (extendedClosedGaussNormalizationChartOpen_isAffineOpen H I E hH e (finSuccEquiv' a)) z hz Q
  have hLy : germ (L₀) y a hy ∈ IsLocalRing.maximalIdeal ((N).presheaf.stalk y) :=
    (hsection (extendedClosedGaussChartPolynomialCoefficient H I E hH e (L₀) a)).mp hvan
  intro hreg
  exact actual_normal_plane_height_one_point_scaled_quotient_nonregular
    H I E hH e hd hind hGauss hvertex s n hs hnlast hn hL0 c hpower
      y (hyheight.trans hQ) a hy hLy ((hregular _).mp hreg)

/-- The pole criterion uses precisely the quotient of the numerator
and normal coefficient in the original stalk, since the homogeneous
source frame cancels in their actual function-field values. -/
theorem actual_stalk_denominator_height_one_prime_local_quotient_pole
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (s n : Fin 4 → E) (hs : s (Fin.last 3) ≠ 0) (hnlast : n (Fin.last 3) = 0)
    (hn : aeval (w) ((O) n) ≠ 0) (hL0 : aeval (w) (L₀) ≠ 0) (c : E)
    (hpower : aeval (w) ((O) s) = algebraMap E (N).functionField c * (aeval (w) (L₀)) ^ d)
    (z : N) (a : Fin 4) (hz : z ∈ V a)
    (Q : PrimeSpectrum ((N).presheaf.stalk z)) (hQ : Q.asIdeal.height = 1)
    (hvan : germ (L₀) z a hz ∈ Q.asIdeal) :
    algebraMap ((N).presheaf.stalk z) (N).functionField (germ ((O) n) z a hz) /
        (algebraMap ((N).presheaf.stalk z) (N).functionField (germ (L₀) z a hz)) ^ d ∉
      fractionPrimeLocalAlgebra ((N).presheaf.stalk z) Q.asIdeal := by
  rw [extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e ((O) n)
      (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH n) z a hz,
    extendedClosedGaussPolynomialCoefficientGerm_value H I E hH e (L₀)
      (linearFormPolynomial_homogeneous _) z a hz, pow_one,
    homogeneous_frame_quotient_cancel _ _ _
      (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e a) d]
  exact actual_stalk_denominator_height_one_prime_scaled_quotient_pole H I E hH e hd hind hGauss
    hvertex s n hs hnlast hn hL0 c hpower z a hz Q hQ hvan

end DimensionFourDependence
