import DimensionFourDependence.SourceEuler
import DimensionFourDependence.Homogeneous
import Mathlib.RingTheory.Localization.NumDen

/-! # Homogeneous fractions from the source Euler constants

The Euler operator preserves every monomial and multiplies its coefficient
by its total degree. A reduced rational fraction killed by this operator
therefore has numerator and denominator in the same homogeneous degree.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The polynomial Euler operator before passage to the fraction field. -/
noncomputable def polynomialEuler (p : MvPolynomial (Fin n) K) :
    MvPolynomial (Fin n) K := ∑ i, X i * pderiv i p

theorem polynomialEuler_coeff (p : MvPolynomial (Fin n) K) (m : Fin n →₀ ℕ) :
    (polynomialEuler p).coeff m = (m.degree : K) * p.coeff m := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [polynomialEuler, map_add, mul_add, Finset.sum_add_distrib,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at *
    rw [hp, hq]
  | monomial s a =>
    have h := (isHomogeneous_monomial a (n := s.degree) rfl).sum_X_mul_pderiv
    change (∑ i : Fin n, X i * pderiv i (monomial s a)).coeff m = _
    rw [h, coeff_smul]
    by_cases hm : s = m
    · subst s
      simp [nsmul_eq_mul]
    · simp [coeff_monomial, hm]

theorem polynomialEuler_totalDegree_le (p : MvPolynomial (Fin n) K) :
    (polynomialEuler p).totalDegree ≤ p.totalDegree := by
  apply totalDegree_le_of_support_subset
  intro m hm
  rw [mem_support_iff, polynomialEuler_coeff] at hm
  exact mem_support_iff.mpr (mul_ne_zero_iff.mp hm).2

theorem sourceEuler_polynomial (p : MvPolynomial (Fin n) K) :
    sourceEuler (K := K) (algebraMap (MvPolynomial (Fin n) K)
      (FractionRing (MvPolynomial (Fin n) K)) p) =
      algebraMap (MvPolynomial (Fin n) K) _ (polynomialEuler p) := by
  rw [sourceEuler, sourceVectorDerivation_apply]
  simp only [rationalCoordinate, rationalPartial_polynomial, polynomialEuler,
    ← map_mul, ← map_sum]

variable [CharZero K]

/-- An Euler eigenvector is homogeneous, and its weight is its degree. -/
theorem polynomialEuler_eigenvector_homogeneous (p : MvPolynomial (Fin n) K)
    (hp : p ≠ 0) (a : K) (he : polynomialEuler p = C a * p) :
    ∃ d : ℕ, p.IsHomogeneous d ∧ a = (d : K) := by
  classical
  obtain ⟨m, hm⟩ := support_nonempty.mpr hp
  have hc : ∀ s, p.coeff s ≠ 0 → (s.degree : K) = a := by
    intro s hs
    have h := congrArg (fun P : MvPolynomial (Fin n) K => P.coeff s) he
    rw [polynomialEuler_coeff, coeff_C_mul] at h
    exact mul_right_cancel₀ hs h
  refine ⟨m.degree, ?_, (hc m (mem_support_iff.mp hm)).symm⟩
  intro s hs
  change Finsupp.weight (fun _ : Fin n => 1) s = m.degree
  rw [← Finsupp.degree_eq_weight_one]
  exact Nat.cast_injective ((hc s hs).trans (hc m (mem_support_iff.mp hm)).symm)

omit [CharZero K] in
/-- A polynomial dividing its Euler derivative is an Euler eigenvector. -/
theorem polynomialEuler_scalar_of_dvd (p : MvPolynomial (Fin n) K)
    (hp : p ≠ 0) (hd : p ∣ polynomialEuler p) :
    ∃ a : K, polynomialEuler p = C a * p := by
  obtain ⟨r, hr⟩ := hd
  have hd0 : r.totalDegree = 0 := by
    by_cases hz : r = 0
    · simp [hz]
    · have hdeg := polynomialEuler_totalDegree_le p
      rw [hr, totalDegree_mul_of_isDomain hp hz] at hdeg
      omega
  refine ⟨r.coeff 0, ?_⟩
  rw [hr, (totalDegree_eq_zero_iff_eq_C.mp hd0), mul_comm]
  simp

/-- Every transcendental source Euler constant has a coprime homogeneous
polynomial numerator and denominator of the same positive degree. -/
theorem sourceEuler_constant_reduced_homogeneous_fraction
    (t : FractionRing (MvPolynomial (Fin n) K)) (ht : Transcendental K t)
    (he : sourceEuler (K := K) t = 0) :
    ∃ p q : MvPolynomial (Fin n) K, ∃ d : ℕ,
      0 < d ∧ p ≠ 0 ∧ q ≠ 0 ∧ p.IsHomogeneous d ∧ q.IsHomogeneous d ∧
      IsRelPrime p q ∧ t = algebraMap _ _ p / algebraMap _ _ q := by
  classical
  let R := MvPolynomial (Fin n) K
  let F := FractionRing R
  obtain ⟨p, q, hrel, hrep⟩ := IsFractionRing.exists_reduced_fraction R t
  have hq : (q : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp q.property
  have hqF : algebraMap R F (q : R) ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective R F).ne hq
  have hfrac : t = algebraMap R F p / algebraMap R F (q : R) := by
    rw [IsFractionRing.mk'_eq_div] at hrep
    exact hrep.symm
  have hp : p ≠ 0 := by
    intro hz
    rw [hfrac, hz, map_zero, zero_div] at ht
    exact ht isAlgebraic_zero
  have hcross : (q : R) * polynomialEuler p = p * polynomialEuler (q : R) := by
    rw [hfrac, Derivation.leibniz_div, sourceEuler_polynomial,
      sourceEuler_polynomial] at he
    simp only [smul_eq_mul] at he
    have hzero := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 (inv_ne_zero hqF))
    apply IsFractionRing.injective R F
    simpa only [map_mul, sub_eq_zero] using hzero
  have hpdiv : p ∣ polynomialEuler p :=
    hrel.dvd_of_dvd_mul_left (hcross.symm ▸ dvd_mul_right p (polynomialEuler (q : R)))
  obtain ⟨a, ha⟩ := polynomialEuler_scalar_of_dvd p hp hpdiv
  have hqa : polynomialEuler (q : R) = C a * (q : R) := by
    apply mul_left_cancel₀ hp
    calc
      p * polynomialEuler (q : R) = (q : R) * polynomialEuler p := hcross.symm
      _ = p * (C a * (q : R)) := by rw [ha]; ring
  obtain ⟨d, hpd, had⟩ := polynomialEuler_eigenvector_homogeneous p hp a ha
  obtain ⟨e, hqe, hae⟩ := polynomialEuler_eigenvector_homogeneous (q : R) hq a hqa
  have hde : d = e := Nat.cast_injective (had.symm.trans hae)
  have hd : 0 < d := by
    by_contra hn
    have hd0 : d = 0 := by omega
    have hpC := eq_C_of_isHomogeneous_zero (hd0 ▸ hpd)
    have hqC := eq_C_of_isHomogeneous_zero (hd0 ▸ hde.symm ▸ hqe)
    have hscalar : t = algebraMap K F (p.coeff 0 / (q : R).coeff 0) := by
      rw [hfrac, hpC, hqC, map_div₀]
      simp only [coeff_C]
      rfl
    rw [hscalar] at ht
    exact ht (isAlgebraic_algebraMap _)
  exact ⟨p, q, d, hd, hp, hq, hpd, hde.symm ▸ hqe, hrel, hfrac⟩

end DimensionFourDependence
