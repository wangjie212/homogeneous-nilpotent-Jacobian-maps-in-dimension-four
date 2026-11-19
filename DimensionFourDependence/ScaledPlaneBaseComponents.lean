import DimensionFourDependence.ScaledPlaneBasePrimeLine
import DimensionFourDependence.VertexLinePrimeIdentification

/-! # Actual scaled-plane base components are full vertex lines

The two-equation height bound supplies the transverse generic coordinate
needed by the projection argument. Its line equations then identify the
component prime with the full original-field vertex-line prime.
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

include hvertex

/-- A height-at-most-two base prime in the scaled-plane case is
exactly a full vertex line. The transverse-coordinate condition and
the original line itself are both constructed. -/
theorem scaled_plane_height_le_two_base_prime_eq_vertexLinePrime
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (s : Fin 4 → E) (a : E) (ha : a ≠ 0)
    (hbase : (O) s - C (a ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)))
    (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime]
    (hheight : Q.height ≤ 2) (hpQ : p ∈ Q) (hqQ : q ∈ Q) :
    s (Fin.last 3) ≠ 0 ∧ H (Fin.last 3) ∉ Q ∧
      ∃ (b : Fin 3 → K) (j : Fin 3), b j ≠ 0 ∧ Q = vertexLinePrime b j := by
  obtain ⟨hs, hH4, b, j, hj, hline⟩ :=
    scaled_plane_base_prime_constructs_vertex_line_equations
      H I E hd hH hind hGauss hvertex e p q hq hrel hparameter s a ha hbase Q hpQ hqQ
      (height_le_two_prime_has_transverse_coordinate Q hheight)
  exact ⟨hs, hH4, b, j, hj,
    prime_eq_vertexLinePrime_of_height_le_two Q hheight b j hj hline⟩

/-- Every actual irreducible component of the original two-equation
base is a full line through the fixed vertex. No off-vertex point,
height bound, line direction, or component classification is assumed. -/
theorem scaled_plane_base_component_eq_vertexLinePrime
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
      Q.height = 2 ∧
      ∃ (b : Fin 3 → K) (j : Fin 3), b j ≠ 0 ∧ Q = vertexLinePrime b j := by
  let : Q.IsPrime := hQ.1.1
  have hh := two_equation_base_minimal_prime_height_le_two p q Q hQ
  obtain ⟨hs, hH4, b, j, hj, he⟩ :=
    scaled_plane_height_le_two_base_prime_eq_vertexLinePrime
      H I E hd hH hind hGauss hvertex e p q hq hrel hparameter s a ha hbase Q hh
      (hQ.1.2 (Ideal.subset_span (by simp)))
      (hQ.1.2 (Ideal.subset_span (by simp)))
  refine ⟨hs, hH4, le_antisymm hh ?_, b, j, hj, he⟩
  rw [he]
  exact vertexLinePrime_height_ge_two b j hj

/-- The actual native root construction yields either its full cone
formula or the exact vertex-line classification of every base component.
The scaled-plane congruence and the height bound are constructed internally. -/
theorem actual_affine_root_alternatives_construct_base_components_or_full_cone
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r, AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∀ (Q : Ideal (MvPolynomial (Fin 4) K)),
        Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes →
        H (Fin.last 3) ∉ Q ∧ Q.height = 2 ∧
          ∃ (b : Fin 3 → K) (j : Fin 3), b j ≠ 0 ∧ Q = vertexLinePrime b j := by
  obtain ⟨s, n, r, hs, hn, hnlast, hnvalue, hnbase, hr, hpower, halt⟩ :=
    actual_affine_root_alternatives_construct_base_power_relation
      H I E hH hd hind hGauss e hvertex p q hq hrel hparameter hdata
  rcases halt with ⟨a, ha, hplane, hbase⟩ | hcone
  · right
    intro Q hQ
    exact (scaled_plane_base_component_eq_vertexLinePrime
      H I E hd hH hind hGauss hvertex e p q hq hrel hparameter s a ha hbase Q hQ).2
  · exact Or.inl ⟨r, hcone⟩

end DimensionFourDependence
