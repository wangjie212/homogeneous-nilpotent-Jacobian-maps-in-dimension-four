import DimensionFourDependence.PolynomialGaussCoverParameter
import DimensionFourDependence.PolynomialParameterFormCoefficients
import DimensionFourDependence.VertexIndependentReducedDenominator

/-! # Polynomial Gauss coefficients and an actual transverse denominator

The original map's homogeneous rational-parameter forms construct a constant
change of the same closed Gauss cover. After that change all coefficients
are polynomials in the parameter. Its reduced homogeneous source quotient
has an actual ternary denominator q=q(x), and its source vertex value is
a nonconstant polynomial in w. All original coordinate values are retained.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K F σ : Type*} [Field K] [Field F] [Algebra K F]

/-- A polynomial-coefficient lift has the same source value using
polynomial evaluation at the actual rational parameter. -/
theorem polynomial_parameter_form_lift_source_value
    (f : RatFunc K →ₐ[K] F) (x : σ → F)
    (Q : MvPolynomial σ (Polynomial K)) (P : MvPolynomial σ (RatFunc K))
    (hQ : MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) Q = P) :
    MvPolynomial.eval₂ (Polynomial.aeval (f RatFunc.X)).toRingHom x Q =
      MvPolynomial.eval₂ f.toRingHom x P := by
  rw [← hQ, MvPolynomial.eval₂_map]
  have hc : f.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K)) =
      (Polynomial.aeval (f RatFunc.X)).toRingHom := by
    apply RingHom.ext
    intro r
    exact rational_function_algHom_polynomial_value f r
  rw [hc]

variable [CharZero K] [IsAlgClosed K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "L₀" => transverseSourceField K
local notation "w₀" => rationalCoordinate (K := K) (Fin.last 3)

omit [Field F] [Algebra K F] in
/-- The original homogeneous map and reduced vertex-dependent Gauss
pencil construct, after a constant parameter change on the same closed
cover, ternary forms with polynomial parameter coefficients and a reduced
homogeneous original source quotient with a nonzero ternary denominator.
No polynomial coefficient lift or new source presentation is supplied. -/
theorem actual_gauss_forms_construct_polynomial_coefficients_and_transverse_denominator
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (p q : MvPolynomial (Fin 4) K) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    {a b : ℕ} (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    (hparameter : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) S₀ p / algebraMap (MvPolynomial (Fin 4) K) S₀ q)
    (hvertex : 0 < p.degreeOf (Fin.last 3) ∨ 0 < q.degreeOf (Fin.last 3))
    (Q : Fin 4 → MvPolynomial (Fin 3) (RatFunc K))
    (hQhom : ∀ i, (Q i).IsHomogeneous d)
    (hQ : ∀ i, MvPolynomial.eval₂ (closedGaussParameterSourceHom H I e).toRingHom
      (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q i) =
        algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) :
    ∃ v : RatFunc K ≃ₐ[K] RatFunc K,
      (v = AlgEquiv.refl ∨ ∃ c : K, v = constantReciprocalParameterEquiv c) ∧
      ∃ (P : Fin 4 → MvPolynomial (Fin 3) (Polynomial K)) (U : Polynomial L₀)
        (p' : MvPolynomial (Fin 4) K) (q₀ : MvPolynomial (Fin 3) K) (D : ℕ),
        (∀ i, (P i).IsHomogeneous d ∧
          MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) (P i) =
            MvPolynomial.map v.symm.toRingHom (Q i) ∧
          MvPolynomial.eval₂ (Polynomial.aeval
            (closedGaussParameterSourceHom H I (v.trans e) RatFunc.X)).toRingHom
            (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (P i) =
              algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) ∧
        0 < U.natDegree ∧ Polynomial.aeval w₀ U =
          closedGaussParameterSourceHom H I (v.trans e) RatFunc.X ∧
        0 < D ∧ p' ≠ 0 ∧ q₀ ≠ 0 ∧ p'.IsHomogeneous D ∧
        (rename Fin.castSucc q₀).IsHomogeneous D ∧ IsRelPrime p' (rename Fin.castSucc q₀) ∧
        closedGaussParameterSourceHom H I (v.trans e) RatFunc.X =
          algebraMap (MvPolynomial (Fin 4) K) S₀ p' /
            algebraMap (MvPolynomial (Fin 4) K) S₀ (rename Fin.castSucc q₀) := by
  classical
  obtain ⟨v, hv, Q', U, hQ', hUdegree, hU⟩ :=
    actual_gauss_forms_construct_polynomial_parameter_on_same_closed_cover
      H I e p q hp0 hq0 hrel hp hq hparameter hvertex Q hQhom hQ
  let f := closedGaussParameterSourceHom H I (v.trans e)
  let : Algebra (Polynomial L₀) S₀ := (Polynomial.aeval w₀).toRingHom.toAlgebra
  let : IsScalarTower L₀ (Polynomial L₀) S₀ := IsScalarTower.of_algebraMap_eq
    (by intro c; exact (Polynomial.aeval_C w₀ c).symm)
  let : IsFractionRing (Polynomial L₀) S₀ := actual_source_vertex_polynomial_isFractionRing K
  have hvalue (i : Fin 4) : MvPolynomial.eval₂ f.toRingHom
      (fun j => algebraMap L₀ S₀ (transverseSourceCoordinate K j)) (Q' i) =
      algebraMap (Polynomial L₀) S₀ (sourceVertexPolynomial K (H i)) := by
    change MvPolynomial.eval₂ f.toRingHom
      (fun j : Fin 3 => rationalCoordinate (K := K) j.castSucc) (Q' i) =
      Polynomial.aeval w₀ (sourceVertexPolynomial K (H i))
    rw [sourceVertexPolynomial_value]
    exact (hQ' i).2.2
  have hex (i : Fin 4) := polynomial_vertex_parameter_homogeneous_form_coefficients_are_polynomial
    (transverseSourceCoordinate K) (transverseSourceCoordinate_algebraicIndependent K)
    f U hUdegree hU (Q' i) (hQ' i).2.1 (sourceVertexPolynomial K (H i)) (hvalue i)
  choose P hPhom hPmap using hex
  obtain ⟨p', q', D, hD, hp', hq', hp'hom, hq'hom, hrel', hparameter'⟩ :=
    actual_closed_gauss_parameter_reduced_homogeneous_source_quotient H hH I (v.trans e)
  obtain ⟨q₀, hq₀, hrename⟩ := reduced_source_quotient_polynomial_vertex_denominator_is_ternary
    p' q' hq' hrel' U (hU.trans hparameter')
  refine ⟨v, hv, P, U, p', q₀, D, ?_, hUdegree, hU, hD, hp', hq₀, hp'hom, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hPhom i, (hPmap i).trans (hQ' i).1, ?_⟩
    exact (polynomial_parameter_form_lift_source_value f _ (P i) (Q' i) (hPmap i)).trans (hQ' i).2.2
  · simpa only [hrename] using hq'hom
  · simpa only [hrename] using hrel'
  · simpa only [hrename] using hparameter'

end DimensionFourDependence
