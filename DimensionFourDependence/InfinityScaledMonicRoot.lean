import DimensionFourDependence.RationalInfinityDegree
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Lifts

/-! # A bounded-degree monic projection is integral in the infinity frame

Scaling the fiber variable by the actual infinity parameter preserves
monicity. The total-degree inequalities on its original coefficients
place every scaled coefficient in the actual infinity valuation ring.
Lifting this polynomial constructs the infinity integrality witness.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {k : Type*} [Field k]

/-- The original polynomial degree bound makes its scaled value regular
in the actual rational-function infinity valuation ring. -/
theorem scaled_polynomial_mem_infinity_of_degree_le
    (p : Polynomial k) (n : ℕ) (hdegree : p.natDegree ≤ n) :
    (RatFunc.X⁻¹ : RatFunc k) ^ n * algebraMap (Polynomial k) (RatFunc k) p ∈
      rationalInfinityRing k := by
  by_cases hp : p = 0
  · subst p
    simp
  have hp' : algebraMap (Polynomial k) (RatFunc k) p ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (Polynomial k) (RatFunc k)).ne hp
  have hX : (RatFunc.X⁻¹ : RatFunc k) ≠ 0 := inv_ne_zero RatFunc.X_ne_zero
  apply (rationalInfinityRing_mem_iff _).mpr
  rw [RatFunc.intDegree_mul (pow_ne_zero n hX) hp', rational_intDegree_pow _ hX,
    RatFunc.intDegree_inv, RatFunc.intDegree_X, RatFunc.intDegree_polynomial]
  have hcast : (p.natDegree : ℤ) ≤ n := by exact_mod_cast hdegree
  linarith

variable {L : Type*} [Field L] [Algebra (RatFunc k) L]
  [Algebra (Polynomial k) L] [IsScalarTower (Polynomial k) (RatFunc k) L]
  [Algebra (rationalInfinityRing k) L]
  [IsScalarTower (rationalInfinityRing k) (RatFunc k) L]

/-- A root of a monic equation whose coefficient degrees satisfy the
original total-degree bound is integral after passing to the infinity
frame. The monic equation over the actual infinity ring is constructed. -/
theorem infinity_scaled_root_isIntegral_of_monic_degree_bounds
    (P : Polynomial (Polynomial k)) (hP : P.Monic)
    (hdegree : ∀ i ≤ P.natDegree, (P.coeff i).natDegree + i ≤ P.natDegree)
    (v : L) (hroot : Polynomial.aeval v P = 0) :
    IsIntegral (rationalInfinityRing k)
      (algebraMap (RatFunc k) L (RatFunc.X⁻¹) * v) := by
  let K := RatFunc k
  let A := algebraMap (Polynomial k) K
  let Q : Polynomial K := P.map A
  have hQ : Q.Monic := hP.map A
  have hQdegree : Q.natDegree = P.natDegree := hP.natDegree_map A
  have hcoeff (i : ℕ) : (Q.scaleRoots (RatFunc.X⁻¹)).coeff i ∈ rationalInfinityRing k := by
    simp only [Polynomial.coeff_scaleRoots, Q, Polynomial.coeff_map, hQdegree]
    by_cases hi : i ≤ P.natDegree
    · have hbound : (P.coeff i).natDegree ≤ P.natDegree - i := by
        have h := hdegree i hi
        omega
      simpa only [mul_comm] using
        scaled_polynomial_mem_infinity_of_degree_le (P.coeff i) (P.natDegree - i) hbound
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi), map_zero, zero_mul]
      exact zero_mem _
  have hlift : Q.scaleRoots (RatFunc.X⁻¹) ∈ Polynomial.lifts
      (algebraMap (rationalInfinityRing k) K) := by
    apply (Polynomial.lifts_iff_coeff_lifts _).mpr
    intro i
    exact ⟨⟨_, hcoeff i⟩, rfl⟩
  obtain ⟨T, hT, _, hTmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift
    ((Polynomial.monic_scaleRoots_iff _).mpr hQ)
  have hQroot : Polynomial.aeval v Q = 0 := by
    change Polynomial.eval₂ (algebraMap K L) v (P.map A) = 0
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((algebraMap K L).comp (algebraMap (Polynomial k) K)) v P = 0
    rw [← IsScalarTower.algebraMap_eq (Polynomial k) K L]
    exact hroot
  refine ⟨T, hTmonic, ?_⟩
  rw [IsScalarTower.algebraMap_eq (rationalInfinityRing k) K L,
    ← Polynomial.eval₂_map, hT]
  exact Polynomial.scaleRoots_aeval_eq_zero hQroot

end DimensionFourDependence
