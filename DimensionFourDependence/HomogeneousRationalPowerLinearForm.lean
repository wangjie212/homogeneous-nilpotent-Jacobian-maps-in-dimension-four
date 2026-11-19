import DimensionFourDependence.SourceEulerLinearFactor
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # A rational dth root of a degree-d homogeneous polynomial is an original linear form -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K
local notation "F₀" => FractionRing (MvPolynomial (Fin n) K)

/-- Differentiating the actual nonzero rational root identity forces
source Euler weight one. No homogeneity of the rational root is assumed. -/
theorem homogeneous_rational_positive_power_root_sourceEuler_weight_one
    (f : F₀) (hf : f ≠ 0) (P : R₀) (d : ℕ) (hd : 0 < d)
    (hP : P.IsHomogeneous d) (hpower : f ^ d = algebraMap R₀ F₀ P) :
    sourceEuler (K := K) f = f := by
  have he := congrArg (sourceEuler (K := K) (n := n)) hpower
  rw [Derivation.leibniz_pow, sourceEuler_homogeneous P hP, ← hpower] at he
  simp only [smul_eq_mul, nsmul_eq_mul] at he
  have hd0 : (d : F₀) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  apply mul_left_cancel₀ (mul_ne_zero hd0 (pow_ne_zero (d - 1) hf))
  calc
    _ = (d : F₀) * f ^ d := by simpa only [mul_assoc] using he
    _ = _ := by rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hd]

/-- Normality of the original polynomial ring makes the actual rational
root regular. Its derived Euler weight then constructs a nonzero linear
form over the original constants, retaining both its exact rational value
and its exact polynomial dth power. -/
theorem homogeneous_rational_positive_power_root_constructs_original_linear_form
    (f : F₀) (hf : f ≠ 0) (P : R₀) (d : ℕ) (hd : 0 < d)
    (hP : P.IsHomogeneous d) (hpower : f ^ d = algebraMap R₀ F₀ P) :
    ∃ a : Fin n → K, a ≠ 0 ∧
      algebraMap R₀ F₀ (linearFormPolynomial a) = f ∧ linearFormPolynomial a ^ d = P := by
  have hint : IsIntegral R₀ (f ^ d) := hpower.symm ▸ isIntegral_algebraMap
  obtain ⟨L, hLvalue⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hd hint
  have hLweight : sourceEuler (K := K) (algebraMap R₀ F₀ L) = algebraMap R₀ F₀ L := by
    rw [hLvalue]
    exact homogeneous_rational_positive_power_root_sourceEuler_weight_one f hf P d hd hP hpower
  have hLhom := sourceEuler_weight_one_polynomial_homogeneous L hLweight
  let a : Fin n → K := fun i => (pderiv i L).coeff 0
  have hLa : L = linearFormPolynomial a := eq_sum_of_isHomogeneous_one hLhom
  have ha : a ≠ 0 := by
    intro h
    apply hf
    rw [← hLvalue, hLa, h]
    simp [linearFormPolynomial]
  refine ⟨a, ha, hLa ▸ hLvalue, ?_⟩
  apply IsFractionRing.injective R₀ F₀
  rw [map_pow, ← hLa, hLvalue, hpower]

end DimensionFourDependence
