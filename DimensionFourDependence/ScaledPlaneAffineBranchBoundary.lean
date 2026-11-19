import DimensionFourDependence.ScaledPlaneNormalizedBaseBranch
import DimensionFourDependence.NativePolynomialGermPointEquations
import DimensionFourDependence.ProjectiveVertexLineNormalSection
import DimensionFourDependence.ActualVertexStalkDenominatorPoles
import DimensionFourDependence.ScaledPlaneVertexGeneralLevels
import DimensionFourDependence.NativeProjectiveLevelClosure
import DimensionFourDependence.ScaledPlaneVertexProjectiveLevels
import DimensionFourDependence.ScaledPlaneLevelTargetEquations
import DimensionFourDependence.ScaledPlaneVertexTargetFibers
import DimensionFourDependence.HyperplaneAffineFiberLocus
import DimensionFourDependence.HyperplaneAffineFiberBranch
import DimensionFourDependence.ScaledPlaneVertexAffineFiberBoundary

/-! # Actual affine solution fields with the constructed vertex in their projective boundary -/

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

local instance scaledPlaneAffineBranchBoundaryIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance scaledPlaneAffineBranchBoundaryNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
local instance scaledPlaneAffineBranchBoundaryTensorDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
noncomputable local instance scaledPlaneAffineBranchBoundaryAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable [Module.Finite (closedGaussParameterField H I) E]

include hvertex

/-- The actual root alternatives construct, for every general level,
an actual field-valued solution of all four original affine equations
with L = 1 and the vertex in that solution's own projective closure.
The solution field, its affine coordinates, and its closure prime are
constructed from a specializing point of the actual normalization.
The full-cone alternative is retained without modification. -/
theorem actual_affine_root_alternatives_construct_affine_solution_vertex_boundary_or_full_cone
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ (s n bS bN : Fin 4 → E) (a : E),
        s (Fin.last 3) ≠ 0 ∧ n (Fin.last 3) = 0 ∧ a ≠ 0 ∧
        ∃ S : Set E, S.Finite ∧ ∀ t : E, t ∉ S →
          (fun i => a ^ d * bS i + t * bN i) ≠ 0 ∧
          (fun i => a ^ d * bS i + t * bN i) ∈ W₀ ∧
          s ⬝ᵥ (fun i => a ^ d * bS i + t * bN i) = a ^ d ∧
          n ⬝ᵥ (fun i => a ^ d * bS i + t * bN i) = t ∧
          ∃ q : N,
            let p := linearHyperplaneProjectiveGraph (L₀) (linearFormPolynomial_homogeneous _) ((f) q)
            let v := fun i => projectivePrimeRatioCoordinate p none (some i)
            aeval v (L₀) = 1 ∧
              (∀ i, aeval v (MvPolynomial.map (ι) (H i)) =
                algebraMap E (projectivePrimeRatioField p none) (a ^ d * bS i + t * bN i)) ∧
              fourthAxisAffineInfinityPoint E ∈ projectiveClosureSet (L := E) v := by
  rcases actual_affine_root_alternatives_construct_vertex_target_levels_or_full_cone
    H I E hd hH hind hGauss hvertex e hdata with hcone |
      ⟨s, n, bS, bN, a, hs, hnlast, ha, x, z, hxz, hzimage, S, hS, hlevels⟩
  · exact Or.inl hcone
  · right
    refine ⟨s, n, bS, bN, a, hs, hnlast, ha, S, hS, ?_⟩
    intro t ht
    obtain ⟨hne, hmem, hsvalue, hnvalue, hclosure⟩ := hlevels t ht
    refine ⟨hne, hmem, hsvalue, hnvalue, ?_⟩
    obtain ⟨q, hq, hqz, hLvalue, houtputs, hboundary⟩ :=
      normalized_target_level_constructs_actual_affine_solution_boundary (N) (f)
        (fun i => MvPolynomial.map (ι) (H i)) d (fun i => (hH i).map (ι))
        (L₀) (linearFormPolynomial_homogeneous _) (fun i => a ^ d * bS i + t * bN i) z hclosure
    rw [hzimage, actual_normal_hyperplane_projective_graph_maps_vertex_to_infinity
      H I E hd hH hind hGauss hvertex] at hboundary
    exact ⟨q, hLvalue, houtputs, hboundary⟩

end DimensionFourDependence

