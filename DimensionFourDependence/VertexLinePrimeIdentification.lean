import DimensionFourDependence.VertexLinePrime

/-! # Identifying height-two primes with their constructed vertex lines

The original line equations factor the generic point through the exact
two-coordinate line parametrization. The height bound then gives equality,
and also shows that a height-at-most-two prime cannot be supported on the
vertex axis alone. No line component or transverse point is assumed.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]

/-- Original cross-coordinate line equations imply containment of the
entire exact line prime, by factoring the prime's actual generic point. -/
theorem vertexLinePrime_le_of_coordinate_relations
    (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime]
    (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0)
    (hline : ∀ i : Fin 3,
      C (b j) * X i.castSucc - C (b i) * X j.castSucc ∈ Q) :
    vertexLinePrime b j ≤ Q := by
  let F := FractionRing (MvPolynomial (Fin 4) K ⧸ Q)
  let x : Fin 4 → F := primeQuotientCoordinate Q
  have heval (P : MvPolynomial (Fin 4) K) : aeval x P = 0 ↔ P ∈ Q := by
    change P ∈ fiberVanishingIdeal (L := K) (primeQuotientCoordinate Q) ↔ P ∈ Q
    rw [primeQuotientCoordinate_relations]
  have hx (i : Fin 3) :
      x i.castSucc = algebraMap K F (b i / b j) * x j.castSucc := by
    have he := (heval _).mpr (hline i)
    simp only [map_sub, map_mul, aeval_C, aeval_X, sub_eq_zero] at he
    have hjF : algebraMap K F (b j) ≠ 0 :=
      (_root_.map_ne_zero (algebraMap K F)).mpr hj
    apply mul_left_cancel₀ hjF
    calc
      algebraMap K F (b j) * x i.castSucc =
          algebraMap K F (b i) * x j.castSucc := he
      _ = algebraMap K F (b j) *
          (algebraMap K F (b i / b j) * x j.castSucc) := by
        have hc : algebraMap K F (b j) *
            (algebraMap K F (b i) / algebraMap K F (b j)) = algebraMap K F (b i) := by
          rw [mul_comm]
          exact div_mul_cancel₀ _ hjF
        rw [map_div₀, ← mul_assoc, hc]
  let φ : MvPolynomial (Fin 2) K →ₐ[K] F :=
    aeval ![x j.castSucc, x (Fin.last 3)]
  have hcomp : φ.comp (vertexLineParameterHom b j) = aeval x := by
    apply MvPolynomial.algHom_ext
    intro ℓ
    refine Fin.lastCases ?_ (fun i => ?_) ℓ
    · simp only [AlgHom.comp_apply, vertexLineParameterHom, aeval_X, Fin.snoc_last]
      simp [φ]
    · simpa [φ, vertexLineParameterHom] using (hx i).symm
  intro P hP
  apply (heval P).mp
  change vertexLineParameterHom b j P = 0 at hP
  rw [← hcomp]
  change φ (vertexLineParameterHom b j P) = 0
  rw [hP, map_zero]

/-- The constructed line equals every height-at-most-two prime
containing its original coordinate equations. -/
theorem prime_eq_vertexLinePrime_of_height_le_two
    (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime] (hQ : Q.height ≤ 2)
    (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0)
    (hline : ∀ i : Fin 3,
      C (b j) * X i.castSucc - C (b i) * X j.castSucc ∈ Q) :
    Q = vertexLinePrime b j := by
  exact (Ideal.eq_of_le_of_height_le (vertexLinePrime b j)
    (vertexLinePrime_le_of_coordinate_relations Q b j hj hline)
    (hQ.trans (vertexLinePrime_height_ge_two b j hj))).symm

/-- Every prime of height at most two has a point off the vertex
in its generic support: it cannot contain all three transverse coordinates. -/
theorem height_le_two_prime_has_transverse_coordinate
    (Q : Ideal (MvPolynomial (Fin 4) K)) [Q.IsPrime] (hQ : Q.height ≤ 2) :
    ∃ i : Fin 3, X i.castSucc ∉ Q := by
  by_contra h
  push_neg at h
  let b : Fin 3 → K := ![0, 0, 1]
  have hj : b 2 ≠ 0 := by simp [b]
  have hline (i : Fin 3) :
      C (b 2) * X i.castSucc - C (b i) * X (2 : Fin 3).castSucc ∈ Q :=
    Q.sub_mem (Q.mul_mem_left _ (h i)) (Q.mul_mem_left _ (h 2))
  have he := prime_eq_vertexLinePrime_of_height_le_two Q hQ b 2 hj hline
  have hmem := h 2
  rw [he] at hmem
  exact vertexLinePrime_pivot_not_mem b 2 hj hmem

/-- Krull's height theorem applies to the actual two-equation base
ideal and bounds every minimal prime by two. -/
theorem two_equation_base_minimal_prime_height_le_two
    (p q : MvPolynomial (Fin 4) K)
    (Q : Ideal (MvPolynomial (Fin 4) K))
    (hQ : Q ∈ (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).minimalPrimes) :
    Q.height ≤ 2 := by
  classical
  have hfin : Q ∈ (Ideal.span (↑({p, q} : Finset (MvPolynomial (Fin 4) K)) :
      Set (MvPolynomial (Fin 4) K))).minimalPrimes := by simpa using hQ
  have hh := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hfin
  exact hh.trans (by exact_mod_cast (show ({p, q} : Finset (MvPolynomial (Fin 4) K)).card ≤ 2 by
    simpa using Finset.card_insert_le p ({q} : Finset (MvPolynomial (Fin 4) K))))

end DimensionFourDependence
