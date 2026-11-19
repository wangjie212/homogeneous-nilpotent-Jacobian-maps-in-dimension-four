import DimensionFourDependence.ScaledPlaneBaseComponents
import DimensionFourDependence.HomogeneousPencilBaseExistence
import DimensionFourDependence.ClosedGaussVertexLineIncidence
import DimensionFourDependence.VertexLineCoefficientExtension

/-! # The actual base line and generic normal plane share the source vertex

The original component, its coefficient-extended full line, the pencil
equation and the vertex evaluation are linked explicitly. This is source
incidence; lifting the intersection to the normalization and proving poles
there are separate remaining steps.
-/

namespace DimensionFourDependence

open MvPolynomial

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
local notation "Mₐ" => RingHom.ker (aeval (Fin.snoc (0 : Fin 3 → E) 1)).toRingHom

include hvertex

/-- Every scaled-plane base component is a full original vertex
line. The same line over the actual coefficient extension lies in every
pencil member and passes through the source vertex, where the actual
normal plane vanishes without containing the whole line. -/
theorem scaled_plane_base_component_constructs_vertex_normal_intersection
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (s : Fin 4 → E) (a : E) (ha : a ≠ 0)
    (hbase : (O) s - C (a ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)))
    (Q : Ideal (MvPolynomial (Fin 4) K))
    (hQ : Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes) :
    s (Fin.last 3) ≠ 0 ∧ H (Fin.last 3) ∉ Q ∧
      ∃ (b : Fin 3 → K) (j : Fin 3), b j ≠ 0 ∧ Q = vertexLinePrime b j ∧
        (∀ P ∈ Q, aeval (Fin.snoc (0 : Fin 3 → K) 1) P = 0) ∧
        (∀ t : E, MvPolynomial.map (ι) p - C t * MvPolynomial.map (ι) q ∈
          vertexLinePrime (fun i => (ι) (b i)) j) ∧
        vertexLinePrime (fun i => (ι) (b i)) j ≤ (Mₐ) ∧
        (L₀) ∈ (Mₐ) ∧ (L₀) ∉ vertexLinePrime (fun i => (ι) (b i)) j := by
  obtain ⟨hs, hH4, hh, b, j, hj, he⟩ :=
    scaled_plane_base_component_eq_vertexLinePrime
      H I E hd hH hind hGauss hvertex e p q hq hrel hparameter s a ha hbase Q hQ
  have hpQ : p ∈ Q := hQ.1.2 (Ideal.subset_span (by simp))
  have hqQ : q ∈ Q := hQ.1.2 (Ideal.subset_span (by simp))
  have hpE := vertexLinePrime_map_mem (ι) b j p (he ▸ hpQ)
  have hqE := vertexLinePrime_map_mem (ι) b j q (he ▸ hqQ)
  have hb : b ≠ 0 := by
    intro hz
    exact hj (congrFun hz j)
  have hinc := actual_closed_gauss_normal_vertex_line_plane_incidence
    H I E hd hH hind hGauss hvertex e b hb j hj
  refine ⟨hs, hH4, b, j, hj, he, ?_, ?_, ?_, hinc.1, hinc.2⟩
  · intro P hP
    exact vertexLinePrime_axis_evaluation_zero b j (1 : K) P (he ▸ hP)
  · intro t
    exact (vertexLinePrime (fun i => (ι) (b i)) j).sub_mem hpE
      ((vertexLinePrime (fun i => (ι) (b i)) j).mul_mem_left _ hqE)
  · intro P hP
    exact vertexLinePrime_axis_evaluation_zero _ j (1 : E) P hP

/-- The native root alternatives construct their own positive
homogeneous original pencil and a nonempty set of base components. In
the scaled-plane branch every component is exactly a vertex line. -/
theorem actual_affine_root_alternatives_construct_nonempty_base_lines_or_full_cone
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    ∃ (p q : MvPolynomial (Fin 4) K) (D : ℕ),
      0 < D ∧ p ≠ 0 ∧ q ≠ 0 ∧ p.IsHomogeneous D ∧ q.IsHomogeneous D ∧
      IsRelPrime p q ∧
      closedGaussParameterSourceHom H I e RatFunc.X =
        algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q ∧
      (∃ Q : Ideal (MvPolynomial (Fin 4) K),
        Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes) ∧
      ((∃ r, AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
        ∀ (Q : Ideal (MvPolynomial (Fin 4) K)),
          Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes →
          H (Fin.last 3) ∉ Q ∧ Q.height = 2 ∧
            ∃ (b : Fin 3 → K) (j : Fin 3), b j ≠ 0 ∧ Q = vertexLinePrime b j) := by
  obtain ⟨p, q, D, Q, hD, hp0, hq0, hp, hq, hrel, hparameter, hQ, hh, hoff⟩ :=
    actual_closed_gauss_parameter_constructs_nonempty_base_component H hH I e
  refine ⟨p, q, D, hD, hp0, hq0, hp, hq, hrel, hparameter, ⟨Q, hQ⟩, ?_⟩
  exact actual_affine_root_alternatives_construct_base_components_or_full_cone
    H I E hd hH hind hGauss hvertex e p q hq0 hrel hparameter hdata

end DimensionFourDependence
