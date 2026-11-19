import DimensionFourDependence.ScaledPlaneBaseProjection
import DimensionFourDependence.VertexLineContainment

/-! # Original base primes satisfy the equations of a vertex line

Apply the constructed independent-parameter projection argument to the
actual generic point of a base prime. The resulting original-field
direction yields all two-by-two transverse line equations in that same
prime. The native root construction supplies these equations in its
scaled-plane branch without assuming any tangent-ratio or line data.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u v

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

/-- Every original base prime off the vertex has a nonzero original
projected direction whose vertex-line equations belong to that prime.
Its fourth output and the scaled form's vertex coefficient are nonzero. -/
theorem scaled_plane_base_prime_constructs_vertex_line_equations
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (s : Fin 4 → E) (a : E) (ha : a ≠ 0)
    (hbase : (O) s - C (a ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)))
    (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime] (hpQ : p ∈ Q) (hqQ : q ∈ Q)
    (hoff : ∃ i : Fin 3, X i.castSucc ∉ Q) :
    s (Fin.last 3) ≠ 0 ∧ H (Fin.last 3) ∉ Q ∧
      ∃ (b : Fin 3 → K) (j : Fin 3), b j ≠ 0 ∧
        ∀ i : Fin 3, C (b j) * X i.castSucc - C (b i) * X j.castSucc ∈ Q := by
  let x := primeQuotientCoordinate Q
  have heval (P : MvPolynomial (Fin 4) K) : aeval x P = 0 ↔ P ∈ Q := by
    change P ∈ fiberVanishingIdeal (L := K) (primeQuotientCoordinate Q) ↔ P ∈ Q
    rw [primeQuotientCoordinate_relations]
  have hx : (fun i : Fin 3 => x i.castSucc) ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hoff
    apply hi
    apply (heval (X i.castSucc)).mp
    rw [aeval_X]
    exact congrFun hz i
  obtain ⟨hs, hH4, c, b, hc, hb, hdir⟩ :=
    scaled_plane_base_power_constructs_constant_projection H I E hd hH hind hGauss hvertex e
      p q hq hrel hparameter s a ha hbase x ((heval p).mpr hpQ) ((heval q).mpr hqQ) hx
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
    simpa only [ne_eq, _root_.funext_iff, Pi.zero_apply, not_forall] using hb
  refine ⟨hs, fun h => hH4 ((heval _).mpr h), b, j, hj, ?_⟩
  intro i
  apply (heval _).mp
  simp only [map_sub, map_mul, aeval_C, aeval_X]
  have hi := congrFun hdir i
  have hj' := congrFun hdir j
  change x i.castSucc = c * algebraMap K _ (b i) at hi
  change x j.castSucc = c * algebraMap K _ (b j) at hj'
  rw [hi, hj']
  ring

/-- The actual native root alternatives either retain the full cone
formula or construct vertex-line equations for every original base
prime off the vertex. No scaled base power relation is assumed. -/
theorem actual_affine_root_alternatives_construct_base_vertex_line_or_full_cone
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hdata : ActualAffineFixedVertexRootAlternatives H I E hH hd hind hGauss) :
    (∃ r, AffineSourceFixedVertexConeRootForm H I E hH hd hind hGauss r) ∨
      ∀ (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime], p ∈ Q → q ∈ Q →
        (∃ i : Fin 3, X i.castSucc ∉ Q) →
        H (Fin.last 3) ∉ Q ∧ ∃ (b : Fin 3 → K) (j : Fin 3), b j ≠ 0 ∧
          ∀ i : Fin 3, C (b j) * X i.castSucc - C (b i) * X j.castSucc ∈ Q := by
  obtain ⟨s, n, r, hs, hn, hnlast, hnvalue, hnbase, hr, hpower, halt⟩ :=
    actual_affine_root_alternatives_construct_base_power_relation
      H I E hH hd hind hGauss e hvertex p q hq hrel hparameter hdata
  rcases halt with ⟨a, ha, hplane, hbase⟩ | hcone
  · right
    intro Q hQ hpQ hqQ hoff
    exact (scaled_plane_base_prime_constructs_vertex_line_equations
      H I E hd hH hind hGauss hvertex e p q hq hrel hparameter s a ha hbase Q hpQ hqQ hoff).2
  · exact Or.inl ⟨r, hcone⟩

/-- The same original vertex line contains every field-valued point
of the original base-prime component after every coefficient extension.
The direction and vertex/output nonvanishing are constructed. -/
theorem scaled_plane_base_prime_all_points_contained_in_vertex_line
    (p q : MvPolynomial (Fin 4) K) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (s : Fin 4 → E) (a : E) (ha : a ≠ 0)
    (hbase : (O) s - C (a ^ d) * (L₀) ^ d ∈
      Ideal.span ({MvPolynomial.map (ι) p, MvPolynomial.map (ι) q} :
        Set (MvPolynomial (Fin 4) E)))
    (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime] (hpQ : p ∈ Q) (hqQ : q ∈ Q)
    (hoff : ∃ i : Fin 3, X i.castSucc ∉ Q) :
    s (Fin.last 3) ≠ 0 ∧ H (Fin.last 3) ∉ Q ∧
      ∃ (b : Fin 3 → K) (j : Fin 3), b j ≠ 0 ∧
        ∀ (F : Type v) [Field F] [Algebra K F] (y : Fin 4 → F),
          (∀ P ∈ Q, aeval y P = 0) →
          y ∈ Submodule.span F ({Fin.snoc (fun i : Fin 3 => algebraMap K F (b i)) 0,
            Fin.snoc (0 : Fin 3 → F) 1} : Set (Fin 4 → F)) := by
  obtain ⟨hs, hH4, b, j, hj, hline⟩ := scaled_plane_base_prime_constructs_vertex_line_equations
    H I E hd hH hind hGauss hvertex e p q hq hrel hparameter s a ha hbase Q hpQ hqQ hoff
  refine ⟨hs, hH4, b, j, hj, ?_⟩
  intro F hF hKF y hy
  exact ideal_vertex_line_equations_all_points_mem_span Q b j hj hline y hy

end DimensionFourDependence
