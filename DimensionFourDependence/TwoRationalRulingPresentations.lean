import DimensionFourDependence.RationalRulingPolynomialIdentity

/-! # The two original generic ruling values give exact restrictions of the same polynomial -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 2500000

variable {K E : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]

/-- Two actual coordinate derivatives and two parameter-algebraic
factored values construct the two rational parameter embeddings and
exact polynomial restrictions of the same original bivariate polynomial.
No algebraic independence or coefficient-comparison assumption is supplied. -/
theorem two_parameter_algebraic_factored_values_construct_exact_rational_presentations
    (Ds Dt : Derivation K E E) (s t : E)
    (hss : Ds s = 1) (hst : Ds t = 0) (hts : Dt s = 0) (htt : Dt t = 1)
    (P : Polynomial (Polynomial K)) (v : E) (d : ℕ)
    (a₁ b₁ a₂ b₂ : Fin 2 → E)
    (ha₁ : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (a₁ i))
    (hb₁ : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (b₁ i))
    (ha₂ : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({s} : Set E)) (a₂ i))
    (hb₂ : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({s} : Set E)) (b₂ i))
    (hP : v = Polynomial.eval₂ (Polynomial.aeval t).toRingHom s P)
    (hfirst : v = (segreRulingPowerPolynomial a₁ b₁ d).eval s)
    (hsecond : v = (segreRulingPowerPolynomial a₂ b₂ d).eval t) :
    ∃ φ₁ φ₂ : RatFunc K →ₐ[K] E, φ₁ RatFunc.X = t ∧ φ₂ RatFunc.X = s ∧
      (P.map (algebraMap (Polynomial K) (RatFunc K))).map φ₁.toRingHom =
        segreRulingPowerPolynomial a₁ b₁ d ∧
      ((Polynomial.Bivariate.swap P).map (algebraMap (Polynomial K) (RatFunc K))).map φ₂.toRingHom =
        segreRulingPowerPolynomial a₂ b₂ d := by
  have ht : Transcendental K t := by
    intro h
    exact one_ne_zero (htt.symm.trans (derivation_zero_of_isAlgebraic Dt t h))
  have hs : Transcendental K s := by
    intro h
    exact one_ne_zero (hss.symm.trans (derivation_zero_of_isAlgebraic Ds s h))
  refine ⟨transcendentalParameterFieldHom t ht, transcendentalParameterFieldHom s hs,
    transcendentalParameterFieldHom_X t ht, transcendentalParameterFieldHom_X s hs, ?_, ?_⟩
  · exact parameter_algebraic_factored_value_constructs_rational_ruling_identity
      Ds s t hss hst ht P a₁ b₁ d ha₁ hb₁ (hP.symm.trans hfirst)
  · exact parameter_algebraic_factored_value_constructs_rational_ruling_identity
      Dt t s htt hts hs (Polynomial.Bivariate.swap P) a₂ b₂ d ha₂ hb₂
      ((bivariate_nested_evaluation_swap P t s).trans (hP.symm.trans hsecond))

end DimensionFourDependence
