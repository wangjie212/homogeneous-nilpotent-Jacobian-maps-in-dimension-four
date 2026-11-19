import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic

/-! # A reduced common parameter denominator for a ternary form

A polynomial with rational-parameter coefficients has a common polynomial
denominator. Choosing one of least degree removes every common constant
zero from its numerator coefficients. Thus each constant denominator root
is an actual coefficient pole, with a nonzero numerator form at that root.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K σ : Type*} [Field K]

/-- Every finite rational-parameter coefficient expansion admits a
nonzero polynomial common denominator and a polynomial numerator form. -/
theorem parameter_form_common_denominator (P : MvPolynomial σ (RatFunc K)) :
    ∃ D : Polynomial K, D ≠ 0 ∧ ∃ N : MvPolynomial σ (Polynomial K),
      MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) N =
        C (algebraMap (Polynomial K) (RatFunc K) D) * P := by
  let M := (nonZeroDivisors (Polynomial K)).map (C (σ := σ))
  obtain ⟨⟨N, s⟩, hs⟩ := IsLocalization.surj M P
  obtain ⟨D, hD, heq⟩ := s.property
  refine ⟨D, mem_nonZeroDivisors_iff_ne_zero.mp hD, N, ?_⟩
  simpa only [MvPolynomial.algebraMap_def, ← heq, MvPolynomial.map_C, mul_comm] using hs.symm

/-- A common denominator of least degree has no removable constant
pole: specialization of its whole numerator form is nonzero at every
constant root of the denominator. -/
theorem parameter_form_reduced_common_denominator (P : MvPolynomial σ (RatFunc K)) :
    ∃ D : Polynomial K, D ≠ 0 ∧ ∃ N : MvPolynomial σ (Polynomial K),
      MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) N =
        C (algebraMap (Polynomial K) (RatFunc K) D) * P ∧
      ∀ a : K, D.eval a = 0 → MvPolynomial.map (Polynomial.evalRingHom a) N ≠ 0 := by
  classical
  let W (k : ℕ) : Prop := ∃ D : Polynomial K, D ≠ 0 ∧ D.natDegree = k ∧
    ∃ N : MvPolynomial σ (Polynomial K),
      MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) N =
        C (algebraMap (Polynomial K) (RatFunc K) D) * P
  have hex : ∃ k, W k := by
    obtain ⟨D, hD, N, hN⟩ := parameter_form_common_denominator P
    exact ⟨D.natDegree, D, hD, rfl, N, hN⟩
  obtain ⟨D, hD, hdegree, N, hN⟩ := Nat.find_spec hex
  refine ⟨D, hD, N, hN, ?_⟩
  intro a ha hzero
  have hdivD : Polynomial.X - Polynomial.C a ∣ D := Polynomial.dvd_iff_isRoot.mpr ha
  have hdivN : C (Polynomial.X - Polynomial.C a) ∣ N := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro m
    apply Polynomial.dvd_iff_isRoot.mpr
    have hz := congrArg (fun Q : MvPolynomial σ K => Q.coeff m) hzero
    rw [MvPolynomial.coeff_map] at hz
    change (N.coeff m).eval a = 0 at hz
    exact hz
  obtain ⟨D', hD'⟩ := hdivD
  obtain ⟨N', hN'⟩ := hdivN
  have hD'0 : D' ≠ 0 := by intro hz; simp [hz] at hD'; exact hD hD'
  have hlin : Polynomial.X - Polynomial.C a ≠ (0 : Polynomial K) := Polynomial.X_sub_C_ne_zero a
  have hcancel : C (algebraMap (Polynomial K) (RatFunc K)
      (Polynomial.X - Polynomial.C a)) ≠ (0 : MvPolynomial σ (RatFunc K)) := by
    exact MvPolynomial.C_ne_zero.mpr (RatFunc.algebraMap_ne_zero hlin)
  have hnew : MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) N' =
      C (algebraMap (Polynomial K) (RatFunc K) D') * P := by
    apply mul_left_cancel₀ hcancel
    simpa only [hN', hD', map_mul, MvPolynomial.map_C, map_mul, mul_assoc] using hN
  have hmin : Nat.find hex ≤ D'.natDegree := Nat.find_min' hex ⟨D', hD'0, rfl, N', hnew⟩
  have hdeg : D.natDegree = 1 + D'.natDegree := by
    rw [hD', Polynomial.natDegree_mul hlin hD'0, Polynomial.natDegree_X_sub_C]
  omega

end DimensionFourDependence
