import DimensionFourDependence.Defs

/-! # Irreducibility of primitive linear incidence equations

A primitive vector of coefficients over a domain gives an irreducible
linear form in independent source coordinates. Any factorization has
a factor of source degree zero; its coefficient divides the entire
primitive vector, so that factor is a unit. This applies in particular
to the polynomial coefficients of a parametrized tangent covector.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The source-linear incidence equation with coefficients in an
arbitrary commutative ring, including a polynomial parameter ring. -/
noncomputable def coefficientLinearForm (v : Fin n → R) : MvPolynomial (Fin n) R :=
  ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i

/-- Each source-coordinate coefficient is exactly its original entry. -/
theorem coefficientLinearForm_coeff (v : Fin n → R) (i : Fin n) :
    (coefficientLinearForm v).coeff (Finsupp.single i 1) = v i := by
  classical
  simp [coefficientLinearForm, coeff_X, Finsupp.single_left_inj one_ne_zero]

/-- The actual source-linear equation is homogeneous of degree one. -/
theorem coefficientLinearForm_homogeneous (v : Fin n → R) :
    (coefficientLinearForm v).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X (v i) i

/-- A nonzero coefficient vector gives a nonzero incidence equation. -/
theorem coefficientLinearForm_ne_zero (v : Fin n → R) (hv : v ≠ 0) :
    coefficientLinearForm v ≠ 0 := by
  intro hz
  apply hv
  funext i
  have he := congrArg (fun p : MvPolynomial (Fin n) R => p.coeff (Finsupp.single i 1)) hz
  simpa [coefficientLinearForm_coeff] using he

variable [IsDomain R]

/-- A primitive nonzero coefficient vector over a domain gives an
irreducible actual incidence equation in the independent source variables. -/
theorem coefficientLinearForm_irreducible
    (v : Fin n → R) (hv : v ≠ 0)
    (hprimitive : ∀ r : R, (∀ i, r ∣ v i) → IsUnit r) :
    Irreducible (coefficientLinearForm v) := by
  have hL0 := coefficientLinearForm_ne_zero v hv
  have hdegree : (coefficientLinearForm v).totalDegree = 1 :=
    (coefficientLinearForm_homogeneous v).totalDegree hL0
  have hconstant (a b : MvPolynomial (Fin n) R)
      (hab : coefficientLinearForm v = a * b) (ha : a.totalDegree = 0) : IsUnit a := by
    have he : a = MvPolynomial.C (a.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp ha
    have hd : a ∣ coefficientLinearForm v := ⟨b, hab⟩
    rw [he] at hd
    have hc := (C_dvd_iff_dvd_coeff (a.coeff 0) (coefficientLinearForm v)).mp hd
    have hu : IsUnit (a.coeff 0) := hprimitive _ (fun i => by
      simpa only [coefficientLinearForm_coeff] using hc (Finsupp.single i 1))
    rw [he]
    exact hu.map MvPolynomial.C
  constructor
  · intro hu
    have he := hu.map (MvPolynomial.constantCoeff : MvPolynomial (Fin n) R →+* R)
    have hz : MvPolynomial.constantCoeff (coefficientLinearForm v) = 0 := by
      simp [coefficientLinearForm]
    rw [hz] at he
    exact not_isUnit_zero he
  · intro a b hab
    have hab0 : a * b ≠ 0 := by rwa [← hab]
    have hdeg := totalDegree_mul_of_isDomain (left_ne_zero_of_mul hab0) (right_ne_zero_of_mul hab0)
    rw [← hab, hdegree] at hdeg
    by_cases ha : a.totalDegree = 0
    · exact Or.inl (hconstant a b hab ha)
    · have hb : b.totalDegree = 0 := by omega
      exact Or.inr (hconstant b a (hab.trans (mul_comm a b)) hb)

end DimensionFourDependence
