import DimensionFourDependence.PrimitiveLinearIncidence

/-! # A parameter-polynomial presentation of the actual linear incidence equation

The two standard option-variable equivalences exchange the independent
parameter with the independent source coordinates. The primitive
source-linear equation is irreducible in this presentation too. Its
parameter coefficients recover exactly the original covector entries.
-/

namespace DimensionFourDependence

open MvPolynomial

variable (K : Type*) [Field K] (n : ℕ)

/-- Exchange the independent polynomial parameter and the independent
source variables using the two actual option-variable equivalences. -/
noncomputable def parameterSourceSwap :
    MvPolynomial (Fin n) (Polynomial K) ≃ₐ[K] Polynomial (MvPolynomial (Fin n) K) :=
  (MvPolynomial.optionEquivRight K (Fin n)).symm.trans (MvPolynomial.optionEquivLeft K (Fin n))

/-- A source variable is a constant polynomial in the parameter. -/
theorem parameterSourceSwap_X (i : Fin n) :
    parameterSourceSwap K n (MvPolynomial.X i) = Polynomial.C (MvPolynomial.X i) := by
  change MvPolynomial.optionEquivLeft K (Fin n)
    ((MvPolynomial.optionEquivRight K (Fin n)).symm (MvPolynomial.X i)) = _
  rw [← MvPolynomial.optionEquivRight_X_some, AlgEquiv.symm_apply_apply,
    MvPolynomial.optionEquivLeft_X_some]

/-- The coefficient parameter becomes the outer polynomial variable. -/
theorem parameterSourceSwap_C_X :
    parameterSourceSwap K n (MvPolynomial.C Polynomial.X) = Polynomial.X := by
  change MvPolynomial.optionEquivLeft K (Fin n)
    ((MvPolynomial.optionEquivRight K (Fin n)).symm (MvPolynomial.C Polynomial.X)) = _
  rw [← MvPolynomial.optionEquivRight_X_none, AlgEquiv.symm_apply_apply,
    MvPolynomial.optionEquivLeft_X_none]

/-- Original scalar coefficients are preserved in both presentations. -/
theorem parameterSourceSwap_C_C (r : K) :
    parameterSourceSwap K n (MvPolynomial.C (Polynomial.C r)) = Polynomial.C (MvPolynomial.C r) := by
  change MvPolynomial.optionEquivLeft K (Fin n)
    ((MvPolynomial.optionEquivRight K (Fin n)).symm (MvPolynomial.C (Polynomial.C r))) = _
  rw [← MvPolynomial.optionEquivRight_C, AlgEquiv.symm_apply_apply,
    MvPolynomial.optionEquivLeft_C]

/-- Every actual polynomial coefficient is carried to its coefficient map. -/
theorem parameterSourceSwap_C (p : Polynomial K) :
    parameterSourceSwap K n (MvPolynomial.C p) = Polynomial.map MvPolynomial.C p := by
  have he : (parameterSourceSwap K n).toRingHom.comp MvPolynomial.C =
      Polynomial.mapRingHom (MvPolynomial.C : K →+* MvPolynomial (Fin n) K) := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa using parameterSourceSwap_C_C K n r
    · simpa using parameterSourceSwap_C_X K n
  exact DFunLike.congr_fun he p

variable {K n}

/-- The actual source-linear incidence equation, viewed as a polynomial
in its independent parameter over the source polynomial ring. -/
noncomputable def parameterIncidencePolynomial (v : Fin n → Polynomial K) :
    Polynomial (MvPolynomial (Fin n) K) := parameterSourceSwap K n (coefficientLinearForm v)

/-- The parameter presentation is the original sum of covector
coefficients multiplied by their independent source coordinates. -/
theorem parameterIncidencePolynomial_eq_sum (v : Fin n → Polynomial K) :
    parameterIncidencePolynomial v =
      ∑ i, Polynomial.map MvPolynomial.C (v i) * Polynomial.C (MvPolynomial.X i) := by
  simp only [parameterIncidencePolynomial, coefficientLinearForm, map_sum, map_mul,
    parameterSourceSwap_C, parameterSourceSwap_X]

/-- The coefficient at each parameter degree is exactly the linear
form with the original covector's coefficients at that degree. -/
theorem parameterIncidencePolynomial_coeff (v : Fin n → Polynomial K) (m : ℕ) :
    (parameterIncidencePolynomial v).coeff m = coefficientLinearForm (fun i => (v i).coeff m) := by
  rw [parameterIncidencePolynomial_eq_sum]
  simp [coefficientLinearForm]

/-- Primitivity of the actual parameter coefficient vector gives
irreducibility of its actual parameter incidence polynomial. -/
theorem parameterIncidencePolynomial_irreducible
    (v : Fin n → Polynomial K) (hv : v ≠ 0)
    (hprimitive : ∀ r : Polynomial K, (∀ i, r ∣ v i) → IsUnit r) :
    Irreducible (parameterIncidencePolynomial v) :=
  (MulEquiv.irreducible_iff (f := (parameterSourceSwap K n).toMulEquiv)).mpr
    (coefficientLinearForm_irreducible v hv hprimitive)

end DimensionFourDependence
