import DimensionFourDependence.ScaledPlaneNormalizedBaseBranch
import DimensionFourDependence.NativePolynomialGermPointEquations
import DimensionFourDependence.ProjectiveVertexLineNormalSection
import DimensionFourDependence.ActualVertexStalkDenominatorPoles
import DimensionFourDependence.ScaledPlaneVertexGeneralLevels
import DimensionFourDependence.NativeProjectiveLevelClosure
import DimensionFourDependence.ScaledPlaneVertexProjectiveLevels
import DimensionFourDependence.ScaledPlaneLevelTargetEquations

/-! # Constructed general target fibers accumulate above the actual source vertex -/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory Topology
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
local notation "A₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss
local notation "W₀" => LinearMap.ker (A₀).toLin'
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "germ" P:max z:max hz:max => extendedClosedGaussPolynomialCoefficientGerm H I E hH e P z (Fin.last 3) hz

local instance scaledPlaneVertexTargetFibersIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance scaledPlaneVertexTargetFibersNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
local instance scaledPlaneVertexTargetFibersTensorDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
noncomputable local instance scaledPlaneVertexTargetFibersAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable [Module.Finite (closedGaussParameterField H I) E]

/-- The target coordinate on the dual ruling basis has its stated
two output-linear values. -/
theorem dual_scaled_target_pairings
    {F : Type*} [Field F] {m : ℕ} (s n bS bN : Fin m → F)
    (hsS : s ⬝ᵥ bS = 1) (hnS : n ⬝ᵥ bS = 0)
    (hsN : s ⬝ᵥ bN = 0) (hnN : n ⬝ᵥ bN = 1) (c t : F) :
    s ⬝ᵥ (fun i => c * bS i + t * bN i) = c ∧
      n ⬝ᵥ (fun i => c * bS i + t * bN i) = t := by
  change s ⬝ᵥ (c • bS + t • bN) = c ∧ n ⬝ᵥ (c • bS + t • bN) = t
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hsS, hsN, hnS, hnN,
    mul_one, mul_zero, add_zero, zero_add, and_self]

include hvertex

/-- The actual root alternatives either retain the full cone form or
construct a normalized point above the vertex where general original
output-target loci accumulate on L ≠ 0. Each target is nonzero, lies in
the actual ruling, and has s-value a^d and n-value equal to its level.
The assertion concerns these explicit equations; it does not yet
identify their closures with the full generic-fiber boundary. -/
theorem actual_affine_root_alternatives_construct_vertex_target_levels_or_full_cone
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ (s n bS bN : Fin 4 → E) (a : E),
        s (Fin.last 3) ≠ 0 ∧ n (Fin.last 3) = 0 ∧ a ≠ 0 ∧
        ∃ x z : N, x ⤳ z ∧ (f) z = fourthAxisProjectivePoint E ∧
          ∃ S : Set E, S.Finite ∧ ∀ t : E, t ∉ S →
            (fun i => a ^ d * bS i + t * bN i) ≠ 0 ∧
            (fun i => a ^ d * bS i + t * bN i) ∈ W₀ ∧
            s ⬝ᵥ (fun i => a ^ d * bS i + t * bN i) = a ^ d ∧
            n ⬝ᵥ (fun i => a ^ d * bS i + t * bN i) = t ∧
            z ∈ closure {y : N | (L₀) ∉ ((f) y).asHomogeneousIdeal ∧
              ∀ i : Fin 4, MvPolynomial.map (ι) (H i) -
                C (a ^ d * bS i + t * bN i) * (L₀) ^ d ∈ ((f) y).asHomogeneousIdeal} := by
  rcases actual_affine_root_alternatives_construct_vertex_projective_levels_or_full_cone
    H I E hd hH hind hGauss hvertex e hdata with hcone |
      ⟨s, n, a, hs, hnlast, ha, hnvalue, hpower, x, z, hxz, hzimage, S, hS, hlevels⟩
  · exact Or.inl hcone
  · right
    have hn : aeval (w) ((O) n) ≠ 0 := by
      intro hzero
      exact hnvalue ((extendedClosedGauss_affine_tensor_native_homogeneous_zero_iff
        H I E hH e ((O) n) (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH n)).mpr hzero)
    obtain ⟨bS, bN, hLI, hbS, hbN, hsS, hnS, hsN, hnN, htargets⟩ :=
      actual_scaled_plane_levels_iff_original_output_target_equations
        H I E hH e hd hind hGauss hvertex s n hs hnlast hn (a ^ d) hpower
    refine ⟨s, n, bS, bN, a, hs, hnlast, ha, x, z, hxz, hzimage, S, hS, ?_⟩
    intro t ht
    have hpair := dual_scaled_target_pairings s n bS bN hsS hnS hsN hnN (a ^ d) t
    have hnonzero : (fun i => a ^ d * bS i + t * bN i) ≠ 0 := by
      intro hzero
      have hz : a ^ d = 0 := by simpa only [hzero, dotProduct_zero] using hpair.1.symm
      exact pow_ne_zero d ha hz
    have hmem : (fun i => a ^ d * bS i + t * bN i) ∈ W₀ :=
      (W₀).add_mem ((W₀).smul_mem (a ^ d) hbS) ((W₀).smul_mem t hbN)
    refine ⟨hnonzero, hmem, hpair.1, hpair.2, ?_⟩
    apply closure_mono _ (hlevels t ht)
    intro y hy
    exact ⟨hy.1, (htargets t y).mp hy.2⟩

end DimensionFourDependence

