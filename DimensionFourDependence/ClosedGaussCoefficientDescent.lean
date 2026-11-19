import DimensionFourDependence.TensorPolynomialDescent
import DimensionFourDependence.ClosedGaussTransverseIndependence

/-! # Actual ternary source expansions descend to the closed Gauss parameter field

Relative closedness of the original closed Gauss field is already
proved. The original reduced vertex-dependent pencil supplies actual
transverse source independence. Thus every algebraic-coefficient
ternary expansion representing an original source function descends
uniquely, and homogeneous map entries retain their original degree.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

universe u

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

variable (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E] [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    (G : Type u) [Field G] [Algebra (FractionRing (MvPolynomial (Fin 4) K)) G] [Algebra E G]
    [IsScalarTower (closedGaussParameterField H I) E G]

/-- The actual reduced vertex-dependent Gauss pencil constructs unique
descent of an entire ternary expansion representing an original source
function. Relative closedness and independence are not supplied. -/
theorem actual_closed_gauss_transverse_polynomial_expansion_descends
    (e : RatFunc K ≃ₐ[K] C₀)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    (P : MvPolynomial (Fin 3) E) (y : S₀)
    (hvalue : aeval (fun i : Fin 3 => algebraMap S₀ G (rationalCoordinate (K := K) i.castSucc)) P = algebraMap S₀ G y) :
    ∃! Q : MvPolynomial (Fin 3) C₀, MvPolynomial.map (algebraMap C₀ E) Q = P ∧
      aeval (fun i : Fin 3 => rationalCoordinate (K := K) i.castSucc) Q = y := by
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  have hi := actual_closed_gauss_vertex_pencil_transverse_source_independent H I e p q hp0 hq0 hrel
    hp hq hparameter hvertex
  obtain ⟨Q, hQ, hvalueQ⟩ := relatively_closed_polynomial_expansion_descends
    (closedGaussParameterField_relatively_closed H I) _ hi P y hvalue
  refine ⟨Q, ⟨hQ, hvalueQ⟩, ?_⟩
  intro R hR
  exact (MvPolynomial.map_injective (algebraMap C₀ E) (algebraMap C₀ E).injective)
    (hR.1.trans hQ.symm)

/-- Every original map entry represented as an algebraic-coefficient
ternary form descends to the actual original closed Gauss field, with
the same homogeneous degree and the exact original source value. -/
theorem actual_closed_gauss_ternary_map_coefficients_descend
    (e : RatFunc K ≃ₐ[K] C₀)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    (P : Fin 4 → MvPolynomial (Fin 3) E) {d : ℕ} (hP : ∀ i, (P i).IsHomogeneous d)
    (hvalue : ∀ i : Fin 4,
      aeval (fun j : Fin 3 => algebraMap S₀ G (rationalCoordinate (K := K) j.castSucc)) (P i) =
        algebraMap S₀ G (algebraMap (MvPolynomial (Fin 4) K) S₀ (H i))) :
    ∃ Q : Fin 4 → MvPolynomial (Fin 3) C₀, ∀ i,
      MvPolynomial.map (algebraMap C₀ E) (Q i) = P i ∧ (Q i).IsHomogeneous d ∧
      aeval (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
        algebraMap (MvPolynomial (Fin 4) K) S₀ (H i) := by
  classical
  have hex (i : Fin 4) : ∃ Q : MvPolynomial (Fin 3) C₀,
      MvPolynomial.map (algebraMap C₀ E) Q = P i ∧
      aeval (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) Q =
        algebraMap (MvPolynomial (Fin 4) K) S₀ (H i) := by
    obtain ⟨Q, hQ, _hunique⟩ := actual_closed_gauss_transverse_polynomial_expansion_descends
      H I E G e p q hp0 hq0 hrel hp hq hparameter hvertex (P i) _ (hvalue i)
    exact ⟨Q, hQ⟩
  choose Q hQ using hex
  refine ⟨Q, ?_⟩
  intro i
  have hhom : (Q i).IsHomogeneous d := IsHomogeneous.of_map (algebraMap C₀ E).injective
    (by rw [(hQ i).1]; exact hP i)
  exact ⟨(hQ i).1, hhom, (hQ i).2⟩

end DimensionFourDependence
