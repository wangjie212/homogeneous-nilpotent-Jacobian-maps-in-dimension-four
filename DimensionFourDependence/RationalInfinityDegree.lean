import DimensionFourDependence.Defs
import Mathlib.FieldTheory.RatFunc.Valuation

/-! # Polynomial degree from regularity at the actual place at infinity -/

namespace DimensionFourDependence

variable (k : Type*) [Field k]

/-- The valuation ring of the actual rational function field at infinity. -/
noncomputable def rationalInfinityRing : ValuationSubring (RatFunc k) := by
  classical
  exact (RatFunc.inftyValuation k).valuationSubring

variable {k}

/-- A rational function is regular at infinity exactly when its integer
degree is nonpositive, including the zero function. -/
theorem rationalInfinityRing_mem_iff (x : RatFunc k) :
    x ∈ rationalInfinityRing k ↔ x.intDegree ≤ 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    simp
  change RatFunc.inftyValuation k x ≤ 1 ↔ x.intDegree ≤ 0
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero k hx]
  exact WithZero.exp_le_one_iff

/-- Integer rational degree scales exactly under powers of a nonzero function. -/
theorem rational_intDegree_pow (x : RatFunc k) (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).intDegree = n * x.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hx) hx, ih]
    push_cast
    ring

/-- If multiplying a polynomial by the nth power of the infinity
uniformizer makes it regular there, its actual degree is at most n. -/
theorem polynomial_degree_le_of_scaled_mem_infinity
    (p : Polynomial k) (n : ℕ)
    (h : (RatFunc.X⁻¹ : RatFunc k) ^ n * algebraMap (Polynomial k) (RatFunc k) p ∈
      rationalInfinityRing k) : p.natDegree ≤ n := by
  by_cases hp : p = 0
  · subst p
    exact Nat.zero_le _
  have hp' : algebraMap (Polynomial k) (RatFunc k) p ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective (Polynomial k) (RatFunc k)).ne hp
  have hX : (RatFunc.X⁻¹ : RatFunc k) ≠ 0 := inv_ne_zero RatFunc.X_ne_zero
  have hd : ((RatFunc.X⁻¹ : RatFunc k) ^ n * algebraMap (Polynomial k) (RatFunc k) p).intDegree =
      (p.natDegree : ℤ) - n := by
    rw [RatFunc.intDegree_mul (pow_ne_zero n hX) hp', rational_intDegree_pow _ hX,
      RatFunc.intDegree_inv, RatFunc.intDegree_X, RatFunc.intDegree_polynomial]
    ring
  have hn := (rationalInfinityRing_mem_iff _).mp h
  rw [hd] at hn
  exact_mod_cast (sub_nonpos.mp hn)

end DimensionFourDependence
