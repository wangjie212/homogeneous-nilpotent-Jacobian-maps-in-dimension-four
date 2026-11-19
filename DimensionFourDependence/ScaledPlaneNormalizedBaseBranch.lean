import DimensionFourDependence.ExtendedPencilVertexLineLift
import DimensionFourDependence.ScaledPlaneBaseVertexIntersection

/-! # The scaled-plane branch constructs normalized base branches through the vertex

All source components and normalization points are constructed. The actual
vertex-annihilating numerator belongs to their extended line primes while
the normal form does not. This retains the data for the zero-germ and pole
comparison, without claiming the remaining normalized pole-order argument.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory Topology
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

/-- A nonzero vertex-annihilating covector and a covector nonzero
at the vertex are independent, with no ruling-coordinate assumption. -/
theorem vertex_covector_pair_linearIndependent
    {F : Type*} [Field F] (s n : Fin 4 → F)
    (hs : s (Fin.last 3) ≠ 0) (hn : n ≠ 0) (hnlast : n (Fin.last 3) = 0) :
    LinearIndependent F ![s, n] := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hlast : c 0 * s (Fin.last 3) = 0 := by
    have he := congrFun hc (Fin.last 3)
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      hnlast, mul_zero, add_zero] using he
  have hc0 : c 0 = 0 := (mul_eq_zero.mp hlast).resolve_right hs
  have hnsmul : c 1 • n = 0 := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, hc0, zero_smul, zero_add] using hc
  have hc1 : c 1 = 0 := (smul_eq_zero.mp hnsmul).resolve_right hn
  fin_cases i
  · exact hc0
  · exact hc1

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "F₀" => FractionRing T₀
local notation "xₐ" => extendedClosedGaussAffineTensorCoordinate H I E
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)
local notation "O" => extendedClosedGaussOutputLinearPolynomial H I E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "π" => extendedClosedGaussNormalizationSchemeMap H I E hH e ≫
  extendedClosedGaussPencilSchemeInclusion H I E hH e

local instance scaledPlaneNormalizedBaseBranchDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain

include hvertex

/-- Each actual base component constructs its own normalized
generic branch through a point above the vertex. The numerator vanishes
on its full source line, whereas the actual normal form does not. -/
theorem scaled_plane_base_component_constructs_normalized_branch_through_vertex
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
        (O) n ∈ vertexLinePrime (fun i => (ι) (b i)) j ∧
        (L₀) ∉ vertexLinePrime (fun i => (ι) (b i)) j ∧
        ∃ x z : N, x ⤳ z ∧
          (π) x = vertexLineProjectiveGenericPoint (fun i => (ι) (b i)) j
            ((_root_.map_ne_zero (ι)).mpr hj) ∧
          (π) z = fourthAxisProjectivePoint E := by
  obtain ⟨hs, hH4, b, j, hj, he, hvertexQ, hmembers, haxis, hLvertex, hLline⟩ :=
    scaled_plane_base_component_constructs_vertex_normal_intersection
      H I E hd hH hind hGauss hvertex e p q hq hrel hparameter s a ha hbase Q hQ
  have hpQ : p ∈ Q := hQ.1.2 (Ideal.subset_span (by simp))
  have hqQ : q ∈ Q := hQ.1.2 (Ideal.subset_span (by simp))
  have hNbase := vertex_output_covector_mem_extended_pencil_base_radical
    H I E hd hH hind hGauss hvertex e p q hq hrel hparameter n hnlast
  have hle : Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
      Set (MvPolynomial (Fin 4) E)) ≤ vertexLinePrime (fun i => (ι) (b i)) j := by
    apply Ideal.span_le.mpr
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl
    · exact vertexLinePrime_map_mem (ι) b j p (he ▸ hpQ)
    · exact vertexLinePrime_map_mem (ι) b j q (he ▸ hqQ)
  have hNline : (O) n ∈ vertexLinePrime (fun i => (ι) (b i)) j :=
    ((Ideal.IsPrime.radical_le_iff (inferInstance :
      (vertexLinePrime (fun i => (ι) (b i)) j).IsPrime)).mpr hle) hNbase
  obtain ⟨x, z, hxz, hx, hz⟩ := original_base_vertex_line_constructs_normalized_branch_and_vertex
    H I E hH e p q hq hrel hparameter b j hj (he ▸ hpQ) (he ▸ hqQ)
  exact ⟨hs, hH4, b, j, hj, he, hNline, hLline, x, z, hxz, hx, hz⟩

/-- The native affine alternatives construct nonzero independent
output coordinates and actual normalized base branches through the
vertex, or retain the full-cone alternative. No component, normalized
point, branch incidence, or independent output pair is supplied. -/
theorem actual_affine_root_alternatives_construct_normalized_base_branches_or_full_cone
    (p q : MvPolynomial (Fin 4) K) {D : ℕ} (hD : 0 < D) (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hp : p.IsHomogeneous D) (hq : q.IsHomogeneous D) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r, AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∃ (s n : Fin 4 → E) (r : F₀) (a : E),
        s (Fin.last 3) ≠ 0 ∧ n (Fin.last 3) = 0 ∧ LinearIndependent E ![s, n] ∧
        aeval (xₐ) ((O) n) ≠ 0 ∧ r ≠ 0 ∧ a ≠ 0 ∧
        r ^ d = aeval (xₐ) ((O) s) ∧ r = algebraMap E F₀ a * aeval (xₐ) (L₀) ∧
        ∀ (Q : Ideal (MvPolynomial (Fin 4) K)),
          Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes →
          H (Fin.last 3) ∉ Q ∧
            ∃ (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0), Q = vertexLinePrime b j ∧
              (O) n ∈ vertexLinePrime (fun i => (ι) (b i)) j ∧
              (L₀) ∉ vertexLinePrime (fun i => (ι) (b i)) j ∧
              ∃ x z : N, x ⤳ z ∧
                (π) x = vertexLineProjectiveGenericPoint (fun i => (ι) (b i)) j
                  ((_root_.map_ne_zero (ι)).mpr hj) ∧
                (π) z = fourthAxisProjectivePoint E := by
  obtain ⟨s, n, r, hs0, hn0, hnlast, hnvalue, hnbase, hr, hpower, halt⟩ :=
    actual_affine_root_alternatives_construct_base_power_relation
      H I E hH hd hind hGauss e hvertex p q hq0 hrel hparameter hdata
  rcases halt with ⟨a, ha, hplane, hbase⟩ | hcone
  · obtain ⟨Q₀, hQ₀, hh, hoff⟩ :=
      positive_homogeneous_coprime_pair_constructs_base_component p q hD hp0 hp hq hrel
    have hs := (scaled_plane_base_component_eq_vertexLinePrime
      H I E hd hH hind hGauss hvertex e p q hq0 hrel hparameter s a ha hbase Q₀ hQ₀).1
    right
    refine ⟨s, n, r, a, hs, hnlast, vertex_covector_pair_linearIndependent s n hs hn0 hnlast,
      hnvalue, hr, ha, hpower, hplane, ?_⟩
    intro Q hQ
    exact (scaled_plane_base_component_constructs_normalized_branch_through_vertex
      H I E hd hH hind hGauss hvertex e p q hq0 hrel hparameter s n hnlast a ha hbase Q hQ).2
  · exact Or.inl ⟨r, hcone⟩

end DimensionFourDependence
