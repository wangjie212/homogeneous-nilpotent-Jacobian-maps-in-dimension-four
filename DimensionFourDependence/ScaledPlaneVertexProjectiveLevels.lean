import DimensionFourDependence.ScaledPlaneNormalizedBaseBranch
import DimensionFourDependence.NativePolynomialGermPointEquations
import DimensionFourDependence.ProjectiveVertexLineNormalSection
import DimensionFourDependence.ActualVertexStalkDenominatorPoles
import DimensionFourDependence.ScaledPlaneVertexGeneralLevels
import DimensionFourDependence.NativeProjectiveLevelClosure
import DimensionFourDependence.ScaledPlaneBasePower

/-! # The actual root alternatives construct projective general levels through the vertex -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory Topology
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "F₀" => FractionRing
  (FractionRing (MvPolynomial (Fin 4) K) ⊗[closedGaussParameterField H I] E)
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "C₀" => closedGaussParameterField H I
local notation "T₀" => FractionRing (MvPolynomial (Fin 4) K) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "V" => extendedClosedGaussNormalizationChartOpen H I E hH e (finSuccEquiv' (Fin.last 3))
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "germ" P:max z:max hz:max => extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z (Fin.last 3) hz

local instance scaledPlaneVertexProjectiveLevelsIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance scaledPlaneVertexProjectiveLevelsNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
local instance scaledPlaneVertexProjectiveLevelsTensorDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
noncomputable local instance scaledPlaneVertexProjectiveLevelsAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable [Module.Finite (closedGaussParameterField H I) E]

/-- The same homogeneous scaled-power identity holds on the actual
normalization when it holds on the original affine source. -/
theorem actual_affine_scaled_power_identity_constructs_native_power
    (S L : MvPolynomial (Fin 4) E) (hS : S.IsHomogeneous d) (hL : L.IsHomogeneous 1)
    (c : E) (hpower : aeval (xₐ) S = algebraMap E (F₀) c * (aeval (xₐ) L) ^ d) :
    aeval (w) S = algebraMap E (N).functionField c * (aeval (w) L) ^ d := by
  have hQ : (S - C c * L ^ d).IsHomogeneous d :=
    hS.sub (by simpa only [one_mul] using (hL.pow d).C_mul c)
  have hzero : aeval (xₐ) (S - C c * L ^ d) = 0 := by
    simp only [map_sub, map_mul, map_pow, aeval_C, hpower, sub_self]
  have hn := (extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff
    H I E hH e _ hQ).mp hzero
  simpa only [map_sub, map_mul, map_pow, aeval_C, sub_eq_zero] using hn

include hvertex

/-- The actual normalized base component meets the closure of every
general homogeneous numerator/normal-power level on its original
denominator open, at a point above the source vertex. -/
theorem scaled_plane_base_component_constructs_vertex_projective_general_levels
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (s n : Fin 4 → E) (hnlast : n (Fin.last 3) = 0)
    (hnvalue : aeval (xₐ) ((O) n) ≠ 0)
    (a : E) (ha : a ≠ 0)
    (hpower : aeval (w) ((O) s) =
      algebraMap E (N).functionField (a ^ d) * (aeval (w) (L₀)) ^ d)
    (hbase : (O) s - C (a ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)))
    (Q : Ideal (MvPolynomial (Fin 4) K))
    (hQ : Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes) :
    s (Fin.last 3) ≠ 0 ∧ H (Fin.last 3) ∉ Q ∧
      ∃ x z : N, x ⤳ z ∧ (f) z = fourthAxisProjectivePoint E ∧
        ∃ S : Set E, S.Finite ∧ ∀ c : E, c ∉ S →
          z ∈ closure {y : N | (L₀) ∉ ((f) y).asHomogeneousIdeal ∧
            (O) n - C c * (L₀) ^ d ∈ ((f) y).asHomogeneousIdeal} := by
  obtain ⟨hs, hH4, x, z, hxz, hzimage, hz, S, hS, hlevels⟩ :=
    scaled_plane_base_component_constructs_vertex_general_level_closure
      H I E hd hH hind hGauss hvertex e p q hq hrel hparameter
      s n hnlast hnvalue a ha hpower hbase Q hQ
  refine ⟨hs, hH4, x, z, hxz, hzimage, S, hS, ?_⟩
  intro c hc
  exact native_local_level_closure_implies_projective_level_closure H I E hH e
    ((O) n) (L₀) hd (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH n)
    (linearFormPolynomial_homogeneous _) c z (Fin.last 3) hz (hlevels c hc)

/-- From the actual affine root alternatives, the original map either
retains its full cone form or constructs a normalized vertex point in
the closure of every general homogeneous quotient level. The original
base component, scaled-power identity, and all local branches are derived. -/
theorem actual_affine_root_alternatives_construct_vertex_projective_levels_or_full_cone
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ (s n : Fin 4 → E) (a : E), s (Fin.last 3) ≠ 0 ∧ n (Fin.last 3) = 0 ∧
        a ≠ 0 ∧ aeval (xₐ) ((O) n) ≠ 0 ∧
        aeval (w) ((O) s) = algebraMap E (N).functionField (a ^ d) * (aeval (w) (L₀)) ^ d ∧
        ∃ x z : N, x ⤳ z ∧ (f) z = fourthAxisProjectivePoint E ∧
          ∃ S : Set E, S.Finite ∧ ∀ c : E, c ∉ S →
            z ∈ closure {y : N | (L₀) ∉ ((f) y).asHomogeneousIdeal ∧
              (O) n - C c * (L₀) ^ d ∈ ((f) y).asHomogeneousIdeal} := by
  obtain ⟨p, q, D, Q, hD, hp0, hq0, hp, hq, hrel, hparameter, hQ, hhQ, hoff⟩ :=
    actual_closed_gauss_parameter_constructs_nonempty_base_component H hH I e
  obtain ⟨s, n, r, hs0, hn0, hnlast, hnvalue, hnbase, hr0, hroot, halt⟩ :=
    actual_affine_root_alternatives_construct_base_power_relation H I E hH hd hind hGauss e
      hvertex p q hq0 hrel hparameter hdata
  rcases halt with ⟨a, ha, hscaled, hbase⟩ | hcone
  · right
    have hpowerAffine : aeval (xₐ) ((O) s) =
        algebraMap E (F₀) (a ^ d) * (aeval (xₐ) (L₀)) ^ d := by
      rw [← hroot, hscaled, mul_pow, map_pow]
    have hpower := actual_affine_scaled_power_identity_constructs_native_power H I E hH e
      ((O) s) (L₀) (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH s)
        (linearFormPolynomial_homogeneous _) (a ^ d) hpowerAffine
    obtain ⟨hs, hH4, x, z, hxz, hzimage, S, hS, hlevels⟩ :=
      scaled_plane_base_component_constructs_vertex_projective_general_levels H I E hd hH hind hGauss
        hvertex e p q hq0 hrel hparameter s n hnlast hnvalue a ha hpower hbase Q hQ
    exact ⟨s, n, a, hs, hnlast, ha, hnvalue, hpower, x, z, hxz, hzimage, S, hS, hlevels⟩
  · exact Or.inl ⟨r, hr0, hcone⟩

end DimensionFourDependence

