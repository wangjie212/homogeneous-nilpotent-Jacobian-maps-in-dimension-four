import DimensionFourDependence.ProjectiveVertexLine
import DimensionFourDependence.VertexLineCoefficientExtension
import DimensionFourDependence.IntegralNormalizationPointLifting
import DimensionFourDependence.AffinePencilBaseRelations
import DimensionFourDependence.ExtendedGaussPencilScheme

/-! # Lifting the original vertex line and its vertex to the actual normalization

The reduced source parameter equation places the full extended original
line on the actual projective pencil. Surjectivity constructs its normalized
generic preimages; integral closedness of the morphism lifts the vertex
specialization on each same branch.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory Topology

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2500000
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
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "Qₑ" => extendedClosedGaussPencilScheme H I E hH e
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "π" => extendedClosedGaussNormalizationSchemeMap H I E hH e
local notation "jₑ" => extendedClosedGaussPencilSchemeInclusion H I E hH e

/-- If both original pencil equations vanish on the exact line,
the entire actual extended source relation ideal vanishes there. -/
theorem extendedClosedGaussPencilIdeal_le_vertexLinePrime
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (b : Fin 3 → K) (j : Fin 3)
    (hp : p ∈ vertexLinePrime b j) (hq' : q ∈ vertexLinePrime b j) :
    extendedClosedGaussPencilIdeal H I E ≤ vertexLinePrime (fun i => (ι) (b i)) j := by
  have hpE := vertexLinePrime_map_mem (ι) b j p hp
  have hqE := vertexLinePrime_map_mem (ι) b j q hq'
  have hJ : extendedClosedGaussPencilIdeal H I E =
      Ideal.span {MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilEquation H I e p q)} := by
    change (fiberVanishingIdeal (L := C₀) (rationalCoordinate (K := K) (n := 4))).map
      (MvPolynomial.map (algebraMap C₀ E)) = _
    rw [actual_closed_gauss_pencil_relation_ideal H I e p q hq hrel hparameter,
      Ideal.map_span, Set.image_singleton]
  rw [hJ]
  apply Ideal.span_le.mpr
  apply Set.singleton_subset_iff.mpr
  have he : MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilEquation H I e p q) =
      MvPolynomial.map (ι) p - C (algebraMap C₀ E (e RatFunc.X)) * MvPolynomial.map (ι) q := by
    rw [closedGaussPencilEquation_eq]
    simp only [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_map]
    rfl
  rw [he]
  exact (vertexLinePrime (fun i => (ι) (b i)) j).sub_mem hpE
    ((vertexLinePrime (fun i => (ι) (b i)) j).mul_mem_left _ hqE)

/-- The actual normalization of the actual extended pencil is
surjective, with no chosen normalization point hypothesis. -/
theorem extendedClosedGaussNormalizationSchemeMap_surjective :
    Function.Surjective (π) := by
  let : IsIntegral Qₑ := extendedClosedGaussPencilScheme_isIntegral H I E hH e
  exact integralSchemeNormalizationMap_surjective Qₑ

/-- Every normalized point over the original line's generic point
specializes on that same branch to a point above the fixed vertex. -/
theorem extended_normalization_given_vertex_line_branch_meets_vertex
    (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0)
    (x : Nₑ)
    (hx : ((π) ≫ (jₑ)) x = vertexLineProjectiveGenericPoint (fun i => (ι) (b i)) j
      ((_root_.map_ne_zero (ι)).mpr hj)) :
    ∃ z : Nₑ, x ⤳ z ∧ ((π) ≫ (jₑ)) z = fourthAxisProjectivePoint E := by
  let : IsFinite (π) := extendedClosedGaussNormalizationSchemeMap_isFinite H I E hH e
  let : IsClosedImmersion (jₑ) :=
    extendedClosedGaussPencilSchemeInclusion_isClosedImmersion H I E hH e
  have hclosed : IsClosedMap ((π) ≫ (jₑ)) :=
    (jₑ).isClosedEmbedding.isClosedMap.comp (π).isClosedMap
  have hs : ((π) ≫ (jₑ)) x ⤳ fourthAxisProjectivePoint E := by
    rw [hx]
    exact vertexLineProjectiveGenericPoint_specializes_vertex _ j _
  obtain ⟨z, hz, he⟩ := hclosed.specializingMap.closure_singleton_subset x hs.mem_closure
  exact ⟨z, specializes_iff_mem_closure.mpr hz, he⟩

/-- The original reduced pencil and a line on its base construct
their own normalized generic branch and a vertex point on its closure. -/
theorem original_base_vertex_line_constructs_normalized_branch_and_vertex
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0)
    (hp : p ∈ vertexLinePrime b j) (hq' : q ∈ vertexLinePrime b j) :
    ∃ x z : Nₑ, x ⤳ z ∧
      ((π) ≫ (jₑ)) x = vertexLineProjectiveGenericPoint (fun i => (ι) (b i)) j
        ((_root_.map_ne_zero (ι)).mpr hj) ∧
      ((π) ≫ (jₑ)) z = fourthAxisProjectivePoint E := by
  let y := vertexLineProjectiveGenericPoint (fun i => (ι) (b i)) j
    ((_root_.map_ne_zero (ι)).mpr hj)
  have hy : y ∈ Set.range (jₑ) := by
    rw [extendedClosedGaussPencilSchemeInclusion_range]
    exact extendedClosedGaussPencilIdeal_le_vertexLinePrime
      H I E e p q hq hrel hparameter b j hp hq'
  obtain ⟨y₀, hy₀⟩ := hy
  obtain ⟨x, hx⟩ := extendedClosedGaussNormalizationSchemeMap_surjective H I E hH e y₀
  have hx' : ((π) ≫ (jₑ)) x = y := by
    change (jₑ) ((π) x) = y
    rw [hx, hy₀]
  obtain ⟨z, hxz, hz⟩ := extended_normalization_given_vertex_line_branch_meets_vertex
    H I E hH e b j hj x hx'
  exact ⟨x, z, hxz, hx', hz⟩

end DimensionFourDependence
