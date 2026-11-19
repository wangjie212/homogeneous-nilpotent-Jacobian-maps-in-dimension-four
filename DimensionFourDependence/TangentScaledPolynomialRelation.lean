import DimensionFourDependence.ParabolicMaximalCoefficient
import Mathlib.RingTheory.Algebraic.Integral

/-! # A tied highest coefficient gives a nonzero polynomial in the tangent ratio

If m_j + N = e + j on the tied support, multiplying the leading
coefficient relation by T^N factors out T^e. Its remaining terms are
exactly c_j (T C)^j. Distinct original vertex indices ensure that the
polynomial over the coefficient field is nonzero.
-/

namespace DimensionFourDependence

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Distinct original vertex indices cannot cancel the coefficients
of their polynomial in one new indeterminate. -/
theorem sparse_coefficient_polynomial_ne_zero
    (s : Finset ℕ) (c : ℕ → F) (j : ℕ) (hj : j ∈ s) (hc : c j ≠ 0) :
    (∑ i ∈ s, Polynomial.C (c i) * Polynomial.X ^ i) ≠ 0 := by
  intro hz
  have he := congrArg (fun p : Polynomial F => p.coeff j) hz
  have hcoeff : (∑ i ∈ s, Polynomial.C (c i) * Polynomial.X ^ i).coeff j = c j := by
    simp [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hj]
  rw [hcoeff, Polynomial.coeff_zero] at he
  exact hc he

/-- Clearing tangent powers in the tied leading relation gives an
actual nonzero coefficient-field polynomial in the tangent-scaled
quadratic coefficient, and therefore proves its algebraicity. -/
theorem tied_coefficient_relation_constructs_algebraic_tangent_ratio
    (s : Finset ℕ) (hs : s.Nonempty) (c : ℕ → F)
    (hc : ∀ j ∈ s, c j ≠ 0) (m : ℕ → ℕ) (e N : ℕ)
    (horder : ∀ j ∈ s, m j + N = e + j)
    (T C : E) (hT : T ≠ 0)
    (hrel : (∑ j ∈ s, algebraMap F E (c j) * T ^ m j * C ^ j) = 0) :
    (∑ j ∈ s, Polynomial.C (c j) * Polynomial.X ^ j) ≠ 0 ∧
      Polynomial.aeval (T * C) (∑ j ∈ s, Polynomial.C (c j) * Polynomial.X ^ j) = 0 ∧
      IsAlgebraic F (T * C) := by
  have hterm (j : ℕ) (hj : j ∈ s) :
      (algebraMap F E (c j) * T ^ m j * C ^ j) * T ^ N =
        T ^ e * (algebraMap F E (c j) * (T * C) ^ j) := by
    calc
      _ = algebraMap F E (c j) * T ^ (m j + N) * C ^ j := by rw [pow_add]; ring
      _ = algebraMap F E (c j) * T ^ (e + j) * C ^ j := by rw [horder j hj]
      _ = _ := by rw [pow_add, mul_pow]; ring
  have he : T ^ e * (∑ j ∈ s, algebraMap F E (c j) * (T * C) ^ j) = 0 := by
    calc
      _ = ∑ j ∈ s, T ^ e * (algebraMap F E (c j) * (T * C) ^ j) := Finset.mul_sum _ _ _
      _ = ∑ j ∈ s, (algebraMap F E (c j) * T ^ m j * C ^ j) * T ^ N :=
        Finset.sum_congr rfl (fun j hj => (hterm j hj).symm)
      _ = (∑ j ∈ s, algebraMap F E (c j) * T ^ m j * C ^ j) * T ^ N :=
        (Finset.sum_mul _ _ _).symm
      _ = 0 := by rw [hrel, zero_mul]
  have hsum : (∑ j ∈ s, algebraMap F E (c j) * (T * C) ^ j) = 0 :=
    (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hT)
  obtain ⟨j, hj⟩ := hs
  have hnonzero := sparse_coefficient_polynomial_ne_zero s c j hj (hc j hj)
  have hroot : Polynomial.aeval (T * C) (∑ j ∈ s, Polynomial.C (c j) * Polynomial.X ^ j) = 0 := by
    simpa only [map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X] using hsum
  exact ⟨hnonzero, hroot, ⟨_, hnonzero, hroot⟩⟩

end DimensionFourDependence
