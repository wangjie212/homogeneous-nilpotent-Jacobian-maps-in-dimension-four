import DimensionFourDependence.ScaledPlaneNormalizedBaseBranch
import DimensionFourDependence.ProjectiveVertexLineNormalSection
import DimensionFourDependence.ProjectivePolynomialQuotientGerm

/-! # The constructed normalized base branch has an actual quotient zero germ

The same normalized branch specializes to a point above the vertex.
Its actual numerator/normal-power quotient is a regular vanishing germ
at the branch generic point. The denominator's actual regular coefficient
vanishes at that vertex point. Pole orders are not asserted here.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory Topology

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "π" => extendedClosedGaussNormalizationSchemeMap H I E hH e ≫
  extendedClosedGaussPencilSchemeInclusion H I E hH e
local notation "U" => (π) ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) E) (X (Fin.last 3))
local notation "c" P => projectivePullbackChartPolynomialHom (N) (π) (Fin.last 3) P

local instance scaledPlaneNormalizedZeroGermIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e

include hvertex

/-- Every actual scaled-plane base component constructs a
normalized vanishing quotient germ and a specialization point above
the vertex where its actual denominator coefficient vanishes. -/
theorem scaled_plane_base_component_constructs_normalized_quotient_zero_germ
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (s n : Fin 4 → E) (hnlast : n (Fin.last 3) = 0) (a : E) (ha : a ≠ 0)
    (hbase : (O) s - C (a ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)))
    (Q : Ideal (MvPolynomial (Fin 4) K))
    (hQ : Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes) :
    s (Fin.last 3) ≠ 0 ∧ H (Fin.last 3) ∉ Q ∧
      ∃ (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0), Q = vertexLinePrime b j ∧
        ∃ x z : N, x ⤳ z ∧
          ∃ (hx : X (Fin.last 3) ∉ ((π) x).asHomogeneousIdeal)
            (hz : X (Fin.last 3) ∉ ((π) z).asHomogeneousIdeal),
            (π) x = vertexLineProjectiveGenericPoint (fun i => (ι) (b i)) j
              ((_root_.map_ne_zero (ι)).mpr hj) ∧
            (π) z = fourthAxisProjectivePoint E ∧
            letI : Nonempty (U) := ⟨⟨x, hx⟩⟩
            ∃ g : (N).presheaf.stalk x,
              algebraMap ((N).presheaf.stalk x) (N).functionField g =
                (N).germToFunctionField (U) (c ((O) n)) /
                  ((N).germToFunctionField (U) (c (L₀))) ^ d ∧
              g ∈ IsLocalRing.maximalIdeal ((N).presheaf.stalk x) ∧
              (N).presheaf.germ (U) z hz (c (L₀)) ∈
                IsLocalRing.maximalIdeal ((N).presheaf.stalk z) := by
  obtain ⟨hs, hH4, b, j, hj, he, hNline, hLline, x, z, hxz, hx, hz⟩ :=
    scaled_plane_base_component_constructs_normalized_branch_through_vertex
      H I E hd hH hind hGauss hvertex e p q hq hrel hparameter s n hnlast a ha hbase Q hQ
  have hx4 : X (Fin.last 3) ∉ ((π) x).asHomogeneousIdeal := by
    rw [hx]
    exact vertexLinePrime_fourth_coordinate_not_mem _ j
  have hz4 : X (Fin.last 3) ∉ ((π) z).asHomogeneousIdeal := by
    rw [hz]
    exact fourthAxisProjectivePoint_fourth_coordinate_not_mem E
  have hNy : (O) n ∈ ((π) x).asHomogeneousIdeal := by
    rw [hx]
    exact hNline
  have hLy : (L₀) ∉ ((π) x).asHomogeneousIdeal := by
    rw [hx]
    exact hLline
  have hb : b ≠ 0 := by
    intro hb0
    exact hj (congrFun hb0 j)
  have hLz : (L₀) ∈ ((π) z).asHomogeneousIdeal := by
    rw [hz]
    exact (actual_normal_section_projective_vertex_line_values
      H I E hd hH hind hGauss hvertex e b hb j hj).1
  refine ⟨hs, hH4, b, j, hj, he, x, z, hxz, hx4, hz4, hx, hz, ?_⟩
  letI : Nonempty (U) := ⟨⟨x, hx4⟩⟩
  obtain ⟨g, hg, hgmem⟩ := projective_polynomial_quotient_constructs_vanishing_germ
    (N) (π) x (Fin.last 3) hx4 ((O) n) (L₀)
    (extendedClosedGaussOutputLinearPolynomial_homogeneous H I E hH n)
    (linearFormPolynomial_homogeneous _) hNy hLy d
  exact ⟨g, hg, hgmem, (projective_pullback_polynomial_germ_mem_maximal_iff
    (N) (π) z (Fin.last 3) hz4 (L₀) (linearFormPolynomial_homogeneous _)).mpr hLz⟩

end DimensionFourDependence
