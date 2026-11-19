import DimensionFourDependence.GenericParameterPole
import DimensionFourDependence.PolynomialParameterRegularity

/-! # The parameter becomes polynomial after a constant change

A rational-parameter form with a nonconstant polynomial vertex value
supplies a polynomial parameter after either the identity change or
u=1/(t-a) for an original constant a. In the absence of finite constant
poles, a nonconstant polynomial value makes t integral. Otherwise the
reduced numerator and its actual constant pole construct the reciprocal.
-/

namespace DimensionFourDependence

variable {K L F σ : Type*} [Field K] [IsAlgClosed K] [Field L] [Field F]
    [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F]
    [Algebra (Polynomial L) F] [IsScalarTower L (Polynomial L) F]
    [IsFractionRing (Polynomial L) F]

/-- A genuine nonconstant polynomial source value of a generic
rational-parameter form constructs a nonconstant polynomial parameter
after one of the paper's constant fractional-linear changes. -/
theorem generic_parameter_form_polynomial_after_constant_change
    (x : σ → L) (hx : AlgebraicIndependent K x)
    (f : RatFunc K →ₐ[K] F)
    (ht : ¬ ∃ c : L, algebraMap L F c = f RatFunc.X)
    (P : MvPolynomial σ (RatFunc K)) (H : Polynomial L) (hHdegree : 0 < H.natDegree)
    (hH : MvPolynomial.eval₂ f.toRingHom (fun i => algebraMap L F (x i)) P =
      algebraMap (Polynomial L) F H) :
    ∃ U : Polynomial L, 0 < U.natDegree ∧
      (algebraMap (Polynomial L) F U = f RatFunc.X ∨
        ∃ a : K, algebraMap (Polynomial L) F U =
          (f RatFunc.X - algebraMap K F a)⁻¹) := by
  classical
  obtain ⟨D, hD, N, hN, hpole⟩ := generic_parameter_form_constructs_reduced_pole_pullback
    x hx f ht P H hH
  by_cases hdegree : D.natDegree = 0
  · have hDc : D = Polynomial.C (D.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdegree
    have hDc0 : D.coeff 0 ≠ 0 := by
      intro hz
      apply hD
      rw [hDc, hz, map_zero]
    let δ : L := algebraMap K L (D.coeff 0)
    have hδ : δ ≠ 0 := by simpa only [map_zero] using (algebraMap K L).injective.ne hDc0
    have hDmap : D.map (algebraMap K L) = Polynomial.C δ := by
      calc
        D.map (algebraMap K L) = (Polynomial.C (D.coeff 0)).map (algebraMap K L) :=
          congrArg (Polynomial.map (algebraMap K L)) hDc
        _ = _ := Polynomial.map_C _
    have hvalue := parameter_form_source_value_cleared_relation x f P D N hN _ hH
    rw [hDmap, Polynomial.aeval_C] at hvalue
    have hrelation : Polynomial.aeval (f RatFunc.X) (parameterNumeratorPolynomial x N) =
        algebraMap (Polynomial L) F (H * Polynomial.C δ) := by
      simpa only [map_mul, ← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply L (Polynomial L) F] using hvalue
    have hn : 0 < (parameterNumeratorPolynomial x N).natDegree := by
      by_contra hpos
      have hC := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos hpos)
      have heq : H * Polynomial.C δ = Polynomial.C ((parameterNumeratorPolynomial x N).coeff 0) := by
        apply IsFractionRing.injective (Polynomial L) F
        have hc := hrelation
        rw [hC, Polynomial.aeval_C] at hc
        simpa only [← Polynomial.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply L (Polynomial L) F] using hc.symm
      have hdeg := congrArg Polynomial.natDegree heq
      rw [Polynomial.natDegree_mul_C hδ, Polynomial.natDegree_C] at hdeg
      omega
    obtain ⟨U, hU⟩ := parameter_regular_of_nonconstant_polynomial_value
      (parameterNumeratorPolynomial x N) hn (f RatFunc.X) (H * Polynomial.C δ) hrelation
    refine ⟨U, ?_, Or.inl hU⟩
    by_contra hpos
    have hC := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos hpos)
    apply ht
    refine ⟨U.coeff 0, ?_⟩
    rw [IsScalarTower.algebraMap_apply L (Polynomial L) F]
    change algebraMap (Polynomial L) F (Polynomial.C (U.coeff 0)) = _
    rw [← hC, hU]
  · have hpos : 0 < D.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdegree)
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root D hpos.ne'
    obtain ⟨U, hUdegree, hU⟩ := hpole a ha
    exact ⟨U, hUdegree, Or.inr ⟨a, hU⟩⟩

end DimensionFourDependence
