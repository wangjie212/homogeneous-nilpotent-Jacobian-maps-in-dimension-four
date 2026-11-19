import DimensionFourDependence.CurveDerivationCompatibility
import Mathlib.Algebra.Polynomial.Derivative

/-! # Repeated integration of nilpotent field derivatives over exact constants -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- A coordinate derivative agrees with every iterated original
polynomial derivative at the actual coordinate value. -/
theorem derivation_iterated_polynomial_evaluation
    (D : Derivation K F F) (t : F) (ht : D t = 1) (P : Polynomial K) (n : ℕ) :
    (D : F → F)^[n] (Polynomial.aeval t P) =
      Polynomial.aeval t (Polynomial.derivative^[n] P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, D.map_aeval, ht,
      smul_eq_mul, mul_one]

/-- Iterated actual field derivatives preserve the original difference. -/
theorem derivation_iterate_sub
    (D : Derivation K F F) (n : ℕ) (a b : F) :
    (D : F → F)^[n] (a - b) = (D : F → F)^[n] a - (D : F → F)^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_sub]

/-- If the exact constants of a coordinate derivative are the original
base field, an element with vanishing (N+1)st derivative is a polynomial
of degree at most N in that original coordinate. The polynomial and all
integration constants are constructed inside the original base field. -/
theorem nilpotent_coordinate_derivative_constructs_polynomial
    (D : Derivation K F F) (t : F) (ht : D t = 1)
    (hconstant : ∀ a : F, D a = 0 → ∃ c : K, algebraMap K F c = a)
    (N : ℕ) (f : F) (hzero : (D : F → F)^[N + 1] f = 0) :
    ∃ P : Polynomial K, P.natDegree ≤ N ∧ f = Polynomial.aeval t P := by
  induction N generalizing f with
  | zero =>
    have hf : D f = 0 := by simpa only [Nat.zero_add, Function.iterate_one] using hzero
    obtain ⟨c, hc⟩ := hconstant f hf
    exact ⟨Polynomial.C c, by simp, by simpa only [Polynomial.aeval_C] using hc.symm⟩
  | succ N ih =>
    have htop : D ((D : F → F)^[N + 1] f) = 0 := by
      simpa only [Function.iterate_succ_apply'] using hzero
    obtain ⟨c, hc⟩ := hconstant _ htop
    have hfact : (((N + 1).factorial : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    let A : Polynomial K := Polynomial.C (c / ((N + 1).factorial : K)) * Polynomial.X ^ (N + 1)
    have hA : Polynomial.derivative^[N + 1] A = Polynomial.C c := by
      dsimp only [A]
      rw [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_C_mul]
      simp only [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one, ← Polynomial.C_mul]
      rw [div_mul_cancel₀ _ hfact]
    have hAval : (D : F → F)^[N + 1] (Polynomial.aeval t A) = algebraMap K F c := by
      rw [derivation_iterated_polynomial_evaluation D t ht A (N + 1), hA, Polynomial.aeval_C]
    have hsub : (D : F → F)^[N + 1] (f - Polynomial.aeval t A) = 0 := by
      rw [derivation_iterate_sub, hAval, ← hc, sub_self]
    obtain ⟨Q, hQdegree, hQ⟩ := ih (f - Polynomial.aeval t A) hsub
    have hAdegree : A.natDegree ≤ N + 1 := by
      dsimp only [A]
      exact Polynomial.natDegree_mul_le.trans (by simp)
    refine ⟨Q + A, Polynomial.natDegree_add_le_of_degree_le
      (hQdegree.trans (Nat.le_succ N)) hAdegree, ?_⟩
    calc
      f = (f - Polynomial.aeval t A) + Polynomial.aeval t A := by ring
      _ = Polynomial.aeval t Q + Polynomial.aeval t A := by rw [hQ]
      _ = Polynomial.aeval t (Q + A) := (map_add _ _ _).symm

/-- On a curve over algebraically closed original constants, repeated
integration gives the original-field polynomial with the exact degree
bound. The constant-field hypothesis is derived from the actual curve
and the coordinate derivative. -/
theorem curve_nilpotent_coordinate_derivative_constructs_polynomial [IsAlgClosed K]
    (D : Derivation K F F) (t : F) (ht : D t = 1) (htr : Algebra.trdeg K F ≤ 1)
    (N : ℕ) (f : F) (hzero : (D : F → F)^[N + 1] f = 0) :
    ∃ P : Polynomial K, P.natDegree ≤ N ∧ f = Polynomial.aeval t P := by
  have hD : D ≠ 0 := by
    intro he
    have hz : D t = 0 := by rw [he]; rfl
    exact one_ne_zero (ht.symm.trans hz)
  exact nilpotent_coordinate_derivative_constructs_polynomial D t ht
    (fun a ha => curve_derivation_constants_are_original D hD htr a ha) N f hzero

end DimensionFourDependence
