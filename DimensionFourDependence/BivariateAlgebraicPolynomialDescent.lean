import DimensionFourDependence.PolynomialDifferentialCoefficients
import DimensionFourDependence.AlgebraicParameterRepeatedIntegration

/-! # Section 5.3: two algebraic ruling polynomials construct an original bivariate polynomial -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K E : Type u} [Field K] [CharZero K] [Field E] [Algebra K E]

/-- Fixing an actual parameter annihilates every actual coefficient
algebraic over its original generated parameter field. -/
theorem derivation_zero_of_algebraic_parameter_constant
    (D : Derivation K E E) (t : E) (ht : D t = 0) (x : E)
    (hx : IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) x) : D x = 0 := by
  let J := IntermediateField.adjoin K ({t} : Set E)
  have hJ : J ≤ derivationConstants D := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact ht
  let : CharZero J := charZero_of_injective_algebraMap (algebraMap K J).injective
  exact derivation_zero_of_isAlgebraic (derivationOverConstantSubfield D J hJ) x hx

/-- Comparing an actual polynomial at a derivative coordinate transfers
nilpotence of the transverse derivative to every original coefficient.
Commutation and the coefficient constant field supply the full comparison. -/
theorem commuting_derivations_polynomial_coefficients_nilpotent
    (Ds Dt : Derivation K E E) (s : E) (hss : Ds s = 1) (hts : Dt s = 0)
    (hcomm : ∀ x, Ds (Dt x) = Dt (Ds x)) (P : Polynomial E)
    (hcoeff : ∀ i, Ds (P.coeff i) = 0) (N : ℕ)
    (hzero : (Dt : E → E)^[N + 1] (P.eval s) = 0) :
    ∀ i, (Dt : E → E)^[N + 1] (P.coeff i) = 0 := by
  let Q := (coefficientPolynomialDerivation Dt : Polynomial E → Polynomial E)^[N + 1] P
  have hconst (n i : ℕ) : Ds ((Dt : E → E)^[n] (P.coeff i)) = 0 := by
    induction n with
    | zero => exact hcoeff i
    | succ n ih => rw [Function.iterate_succ_apply', hcomm, ih, map_zero]
  have hQcoeff (i : ℕ) : Ds (Q.coeff i) = 0 := by
    rw [coefficientPolynomialDerivation_iterate_coeff]
    exact hconst (N + 1) i
  have hQvalue : Q.eval s = 0 :=
    (coefficientPolynomialDerivation_iterate_eval Dt s hts P (N + 1)).symm.trans hzero
  have hQ : Q = 0 := polynomial_constant_coefficients_eval_zero_implies_zero Ds s hss Q hQcoeff hQvalue
  intro i
  have hi := congrArg (fun A : Polynomial E => A.coeff i) hQ
  simpa only [Q, coefficientPolynomialDerivation_iterate_coeff, Polynomial.coeff_zero] using hi

/-- Two actual bounded polynomial descriptions, whose coefficients are
algebraic over the opposite original parameter, construct one nonzero
polynomial over the original closed field. Its two original coordinate
degrees satisfy the corresponding independent bounds. -/
theorem two_algebraic_parameter_polynomials_construct_bivariate_polynomial [IsAlgClosed K]
    (Ds Dt : Derivation K E E) (s t : E)
    (hss : Ds s = 1) (hst : Ds t = 0) (hts : Dt s = 0) (htt : Dt t = 1)
    (hcomm : ∀ x, Ds (Dt x) = Dt (Ds x))
    (P Q : Polynomial E) (hP : P ≠ 0) (M N : ℕ)
    (hPdegree : P.natDegree ≤ M) (hQdegree : Q.natDegree ≤ N)
    (hPcoeff : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set E)) (P.coeff i))
    (hQcoeff : ∀ i, IsAlgebraic (IntermediateField.adjoin K ({s} : Set E)) (Q.coeff i))
    (hvalue : P.eval s = Q.eval t) :
    ∃ B : Polynomial (Polynomial K), B ≠ 0 ∧ B.natDegree ≤ M ∧
      (∀ i, (B.coeff i).natDegree ≤ N) ∧
      P.eval s = Polynomial.eval₂ (Polynomial.aeval t).toRingHom s B := by
  classical
  have hPconst (i : ℕ) : Ds (P.coeff i) = 0 :=
    derivation_zero_of_algebraic_parameter_constant Ds t hst _ (hPcoeff i)
  have hQconst (i : ℕ) : Dt (Q.coeff i) = 0 :=
    derivation_zero_of_algebraic_parameter_constant Dt s hts _ (hQcoeff i)
  have hzero : (Dt : E → E)^[N + 1] (P.eval s) = 0 := by
    rw [hvalue]
    exact constant_coefficient_polynomial_iterated_derivative_zero Dt t htt Q hQconst N hQdegree
  have hnil := commuting_derivations_polynomial_coefficients_nilpotent Ds Dt s hss hts hcomm P hPconst N hzero
  have hex (i : ℕ) : ∃ A : Polynomial K, A.natDegree ≤ N ∧ P.coeff i = Polynomial.aeval t A :=
    algebraic_parameter_nilpotent_derivative_constructs_polynomial Dt t htt _ (hPcoeff i) N (hnil i)
  choose A hAdegree hAvalue using hex
  let B : Polynomial (Polynomial K) := ∑ i ∈ P.support, Polynomial.monomial i (A i)
  have hmap : B.map (Polynomial.aeval t).toRingHom = P := by
    simp only [B, Polynomial.map_sum, Polynomial.map_monomial]
    change (∑ i ∈ P.support, Polynomial.monomial i (Polynomial.aeval t (A i))) = P
    simp_rw [← hAvalue]
    exact P.sum_monomial_eq
  have hB : B ≠ 0 := by
    intro hz
    rw [hz, Polynomial.map_zero] at hmap
    exact hP hmap.symm
  have hcoeffB (i : ℕ) : B.coeff i = if i ∈ P.support then A i else 0 := by
    simp [B, Polynomial.coeff_monomial, eq_comm]
  have hdegreeB : B.natDegree ≤ M := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have hPi : P.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (hPdegree.trans_lt hi)
    have hni : i ∉ P.support := by simpa only [Polynomial.mem_support_iff, not_not] using hPi
    simp only [hcoeffB, hni, ite_false]
  have hdegreeCoeff (i : ℕ) : (B.coeff i).natDegree ≤ N := by
    rw [hcoeffB]
    split_ifs
    · exact hAdegree i
    · simp
  refine ⟨B, hB, hdegreeB, hdegreeCoeff, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hmap]

end DimensionFourDependence
