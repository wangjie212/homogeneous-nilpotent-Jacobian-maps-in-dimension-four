import DimensionFourDependence.NativeScaledPlanePoleCriterion
import DimensionFourDependence.FixedVertexScaledOutputSpan

/-! # The original fixed-vertex data force poles over original source divisors -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    [Module.Finite (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" a:max => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' a)
local notation "m" => extendedClosedGaussNormalizationSourceMorphism H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E

local instance fixedVertexScaledPlanePolesIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance fixedVertexScaledPlanePolesAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

include hvertex

/-- Original fixed-vertex coefficients and the scaled-plane power
identity exclude quotient regularity at every actual denominator zero
over an original source divisor. The independent ruling restrictions,
component-span coefficients, primitive factorization and degree bound
are all constructed; none is assumed. -/
theorem actual_fixed_vertex_scaled_plane_quotient_nonregular_over_source_divisor
    (s n : Fin 4 → E) (hs : s (Fin.last 3) ≠ 0) (hnlast : n (Fin.last 3) = 0)
    (hn : aeval (w) ((O) n) ≠ 0) (hL0 : aeval (w) (L₀) ≠ 0) (c : E)
    (hpower : aeval (w) ((O) s) = algebraMap E (N).functionField c * (aeval (w) (L₀)) ^ d)
    (z : N) (hcodim : Order.coheight ((m) z) = 1) (a : Fin 4) (ha : z ∈ V a)
    (hlmax : extendedClosedGaussPolynomialCoefficientGerm H I E hH e (L₀) z a ha ∈
      IsLocalRing.maximalIdeal ((N).presheaf.stalk z)) :
    ¬ IsLocalization.IsInteger ((N).presheaf.stalk z)
      (aeval (w) ((O) n) / (aeval (w) (L₀)) ^ d) := by
  obtain ⟨hpair, bS, bN, hspan⟩ :=
    fixed_vertex_scaled_output_covectors_construct_original_output_span
      H I E hH e hd hind hGauss hvertex s n hs hnlast hn
  obtain ⟨g, P, c₀, hc₀, hg, hgh, hP, hprim, hHP, hPdeg⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  have hgdeg : g.totalDegree < d := by
    rw [hgh.totalDegree hg]
    omega
  exact no_native_scaled_plane_quotient_regular_over_source_divisor
    H I E hH e s n (L₀) (linearFormPolynomial_homogeneous _) hL0 c hpower bS bN hspan
    z hcodim a ha hlmax P g hg hgh hP hprim hHP hgdeg

end DimensionFourDependence
