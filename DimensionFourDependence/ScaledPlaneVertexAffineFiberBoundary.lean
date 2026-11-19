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

/-! # The constructed vertex becomes an infinity point of general affine target fibers -/

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

local instance scaledPlaneVertexAffineFiberBoundaryIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance scaledPlaneVertexAffineFiberBoundaryNoetherian : IsNoetherian N :=
  extendedClosedGaussNormalizationScheme_isNoetherian H I E hH e
local instance scaledPlaneVertexAffineFiberBoundaryTensorDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
noncomputable local instance scaledPlaneVertexAffineFiberBoundaryAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

variable [Module.Finite (closedGaussParameterField H I) E]

/-- The actual fourth source axis at infinity of the original
four-coordinate affine space, with none the homogenizing coordinate. -/
noncomputable def fourthAxisAffineInfinityPoint (F : Type u) [Field F] :
    ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) F) :=
  projectiveCoordinatePoint (fun j : Option (Fin 4) => j.elim 0 (Fin.snoc (0 : Fin 3 → F) 1))
    (option_graph_coordinates_ne_zero _ fourthAxisVector_ne_zero _)

/-- This fixed source direction is actually on the affine infinity
hyperplane, not just on a projective target level. -/
theorem fourthAxisAffineInfinityPoint_mem_infinity :
    X none ∈ (fourthAxisAffineInfinityPoint E).asHomogeneousIdeal := by
  unfold fourthAxisAffineInfinityPoint
  apply (projectiveCoordinatePoint_mem_homogeneous _ _ (isHomogeneous_X (R := E) none)).mpr
  simp only [aeval_X, Option.elim_none]

include hvertex

/-- The actual original normal form vanishes at the specified vertex,
so the L = 1 graph sends that vertex to its original affine infinity
direction, retaining all four original source coordinates. -/
theorem actual_normal_hyperplane_projective_graph_maps_vertex_to_infinity :
    linearHyperplaneProjectiveGraph (L₀) (linearFormPolynomial_homogeneous _)
      (fourthAxisProjectivePoint E) = fourthAxisAffineInfinityPoint E := by
  have hvalue : aeval (Fin.snoc (0 : Fin 3 → E) 1) (L₀) = 0 := by
    simp only [linearFormPolynomial, map_sum, map_mul, aeval_C, aeval_X]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      Fin.snoc_last, mul_one, zero_add]
    exact extended_chosen_ruling_fixed_vertex_last_column H I E hH hd hind hGauss hvertex 0
  unfold fourthAxisProjectivePoint
  rw [linearHyperplaneProjectiveGraph_coordinatePoint, hvalue]
  rfl

include e

/-- The actual root alternatives construct a source vertex at infinity
of the projective closure of every general original affine target fiber
with L fixed to one, or retain their complete cone alternative. The
statement concerns the explicit original affine fibers over E; passage
to the generic output field remains a separate step. -/
theorem actual_affine_root_alternatives_construct_general_affine_fiber_vertex_infinity_or_full_cone
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r : F₀, r ≠ 0 ∧ AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ (s n bS bN : Fin 4 → E) (a : E),
        s (Fin.last 3) ≠ 0 ∧ n (Fin.last 3) = 0 ∧ a ≠ 0 ∧
        ∃ S : Set E, S.Finite ∧ ∀ t : E, t ∉ S →
          (fun i => a ^ d * bS i + t * bN i) ≠ 0 ∧
          (fun i => a ^ d * bS i + t * bN i) ∈ W₀ ∧
          s ⬝ᵥ (fun i => a ^ d * bS i + t * bN i) = a ^ d ∧
          n ⬝ᵥ (fun i => a ^ d * bS i + t * bN i) = t ∧
          fourthAxisAffineInfinityPoint E ∈ closure
            (hyperplaneAffineFiberProjectiveLocus (fun i => MvPolynomial.map (ι) (H i)) d (L₀)
              (fun i => a ^ d * bS i + t * bN i)) := by
  rcases actual_affine_root_alternatives_construct_vertex_target_levels_or_full_cone
    H I E hd hH hind hGauss hvertex e hdata with hcone |
      ⟨s, n, bS, bN, a, hs, hnlast, ha, x, z, hxz, hzimage, S, hS, hlevels⟩
  · exact Or.inl hcone
  · right
    refine ⟨s, n, bS, bN, a, hs, hnlast, ha, S, hS, ?_⟩
    intro t ht
    obtain ⟨hne, hmem, hsvalue, hnvalue, hclosure⟩ := hlevels t ht
    refine ⟨hne, hmem, hsvalue, hnvalue, ?_⟩
    let P : Fin 4 → MvPolynomial (Fin 4) E := fun i => MvPolynomial.map (ι) (H i)
    let Y : Fin 4 → E := fun i => a ^ d * bS i + t * bN i
    have hsource : fourthAxisProjectivePoint E ∈ closure (hyperplaneTargetLevelLocus P d (L₀) Y) := by
      have hi := mem_closure_image (f).continuous.continuousAt hclosure
      rw [hzimage] at hi
      apply closure_mono _ hi
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    have hlift := linearHyperplaneProjectiveGraph_maps_level_closure_into_affine_fiber_closure
      P d (L₀) (linearFormPolynomial_homogeneous _) Y (fourthAxisProjectivePoint E) hsource
    rwa [actual_normal_hyperplane_projective_graph_maps_vertex_to_infinity H I E hd hH hind hGauss hvertex] at hlift

end DimensionFourDependence

