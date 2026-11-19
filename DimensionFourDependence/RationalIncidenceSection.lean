import DimensionFourDependence.ParameterizedLinearIncidence
import DimensionFourDependence.RationalPartial

/-! # A rational section forces a parametrized normal curve to be linear

The primitive source-linear incidence equation is irreducible over the
source polynomial ring. In positive parameter degree it is primitive
there, so Gauss's lemma preserves its irreducibility in the actual source
fraction field. A rational root forces degree one. Every original
covector entry consequently has parameter degree at most one.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- Evaluation of the actual incidence equation in the original source
fraction field is the original covector-coordinate pairing. -/
theorem parameterIncidencePolynomial_eval_fraction
    (v : Fin n → Polynomial K) (t : FractionRing (MvPolynomial (Fin n) K)) :
    Polynomial.eval₂ (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)))
      t (parameterIncidencePolynomial v) =
      ∑ i, Polynomial.aeval t (v i) * rationalCoordinate (K := K) i := by
  rw [parameterIncidencePolynomial_eq_sum]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_map,
    Polynomial.eval₂_C]
  rfl

/-- An irreducible polynomial over a GCD domain with a root in its
actual fraction field has degree at most one. -/
theorem irreducible_polynomial_fraction_root_natDegree_le_one
    {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
    (p : Polynomial R) (hp : Irreducible p) (t : FractionRing R)
    (ht : Polynomial.eval₂ (algebraMap R (FractionRing R)) t p = 0) : p.natDegree ≤ 1 := by
  by_cases hd : p.natDegree = 0
  · omega
  · have hprim := hp.isPrimitive hd
    have hi : Irreducible (Polynomial.map (algebraMap R (FractionRing R)) p) :=
      (hprim.irreducible_iff_irreducible_map_fraction_map (K := FractionRing R)).mp hp
    have hroot : Polynomial.IsRoot (Polynomial.map (algebraMap R (FractionRing R)) p) t := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map] using ht
    have he : (Polynomial.map (algebraMap R (FractionRing R)) p).natDegree = 1 :=
      Polynomial.natDegree_eq_of_degree_eq_some (n := 1)
        (Polynomial.degree_eq_one_of_irreducible_of_root hi hroot)
    rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective R (FractionRing R))] at he
    exact he.le

/-- The actual incidence polynomial of a primitive parameter covector
has parameter degree at most one if the covector annihilates the actual
source vector at a rationally selected parameter value. -/
theorem parameterIncidencePolynomial_natDegree_le_one_of_rational_section
    (v : Fin n → Polynomial K) (hv : v ≠ 0)
    (hprimitive : ∀ r : Polynomial K, (∀ i, r ∣ v i) → IsUnit r)
    (t : FractionRing (MvPolynomial (Fin n) K))
    (hsection : ∑ i, Polynomial.aeval t (v i) * rationalCoordinate (K := K) i = 0) :
    (parameterIncidencePolynomial v).natDegree ≤ 1 := by
  exact irreducible_polynomial_fraction_root_natDegree_le_one _
    (parameterIncidencePolynomial_irreducible v hv hprimitive) t
    ((parameterIncidencePolynomial_eval_fraction v t).trans hsection)

/-- The rational section forces every actual primitive covector entry
to be linear in its parameter, over the original coefficient field. -/
theorem primitive_covector_natDegree_le_one_of_rational_section
    (v : Fin n → Polynomial K) (hv : v ≠ 0)
    (hprimitive : ∀ r : Polynomial K, (∀ i, r ∣ v i) → IsUnit r)
    (t : FractionRing (MvPolynomial (Fin n) K))
    (hsection : ∑ i, Polynomial.aeval t (v i) * rationalCoordinate (K := K) i = 0) :
    ∀ i, (v i).natDegree ≤ 1 := by
  have hd := parameterIncidencePolynomial_natDegree_le_one_of_rational_section v hv hprimitive t hsection
  intro i
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  have hc := Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hm)
  rw [parameterIncidencePolynomial_coeff] at hc
  have he := congrArg (fun p : MvPolynomial (Fin n) K => p.coeff (Finsupp.single i 1)) hc
  simpa [coefficientLinearForm_coeff] using he

end DimensionFourDependence
