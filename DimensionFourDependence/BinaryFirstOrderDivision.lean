import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-! # Exact binary polynomial division along a doubled coordinate line

Every polynomial has an exact expression consisting of its constant,
its first u coefficient, a multiple of u^2, and v times a polynomial.
The latter polynomial has constant equal to the original first v
derivative. This supplies the local unit in a simple-root intersection
directly from its original polynomial, without an explicit quadratic
coefficient presentation or a power-series theorem.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F : Type*} [Field F]

/-- Exact division by u^2 and v, retaining both original first derivatives. -/
theorem binary_first_order_polynomial_division (P : MvPolynomial (Fin 2) F) :
    ∃ R Q : MvPolynomial (Fin 2) F,
      P = C (aeval (fun _ : Fin 2 => (0 : F)) P) +
        C (aeval (fun _ : Fin 2 => (0 : F)) (pderiv 0 P)) * X 0 + X 0 ^ 2 * R + X 1 * Q ∧
      aeval (fun _ : Fin 2 => (0 : F)) Q =
        aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, 0, by simp, by simp⟩
  | add P S hP hS =>
      obtain ⟨R, Q, hP, hQ⟩ := hP
      obtain ⟨T, U, hS, hU⟩ := hS
      refine ⟨R + T, Q + U, ?_, ?_⟩
      · conv_lhs => rw [hP, hS]
        simp only [map_add]
        ring
      · simp only [map_add, hQ, hU]
  | mul_X P i hP =>
      obtain ⟨R, Q, hP, hQ⟩ := hP
      fin_cases i
      · change ∃ R Q : MvPolynomial (Fin 2) F,
          P * X 0 = C (aeval (fun _ : Fin 2 => (0 : F)) (P * X 0)) +
            C (aeval (fun _ : Fin 2 => (0 : F)) (pderiv 0 (P * X 0))) * X 0 + X 0 ^ 2 * R + X 1 * Q ∧
          aeval (fun _ : Fin 2 => (0 : F)) Q = aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 (P * X 0))
        have hv : aeval (fun _ : Fin 2 => (0 : F)) (P * X 0) = 0 := by simp
        have hd0 : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 0 (P * X 0)) =
            aeval (fun _ : Fin 2 => (0 : F)) P := by simp [pderiv_X]
        have hd1 : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 (P * X 0)) = 0 := by simp [pderiv_X]
        refine ⟨C (aeval (fun _ : Fin 2 => (0 : F)) (pderiv 0 P)) + X 0 * R, X 0 * Q, ?_, ?_⟩
        · rw [hv, hd0, map_zero, zero_add]
          conv_lhs => rw [hP]
          ring
        · rw [hd1]
          simp
      · change ∃ R Q : MvPolynomial (Fin 2) F,
          P * X 1 = C (aeval (fun _ : Fin 2 => (0 : F)) (P * X 1)) +
            C (aeval (fun _ : Fin 2 => (0 : F)) (pderiv 0 (P * X 1))) * X 0 + X 0 ^ 2 * R + X 1 * Q ∧
          aeval (fun _ : Fin 2 => (0 : F)) Q = aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 (P * X 1))
        have hv : aeval (fun _ : Fin 2 => (0 : F)) (P * X 1) = 0 := by simp
        have hd0 : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 0 (P * X 1)) = 0 := by simp [pderiv_X]
        have hd1 : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 (P * X 1)) =
            aeval (fun _ : Fin 2 => (0 : F)) P := by simp [pderiv_X]
        refine ⟨0, P, ?_, hd1.symm⟩
        rw [hv, hd0, map_zero]
        ring

/-- For a polynomial through the origin the exact decomposition
has no constant term, and its v factor has the original v derivative. -/
theorem binary_origin_polynomial_division (P : MvPolynomial (Fin 2) F)
    (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0) :
    ∃ R Q : MvPolynomial (Fin 2) F,
      P = C (aeval (fun _ : Fin 2 => (0 : F)) (pderiv 0 P)) * X 0 + X 0 ^ 2 * R + X 1 * Q ∧
      aeval (fun _ : Fin 2 => (0 : F)) Q =
        aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) := by
  obtain ⟨R, Q, h, hQ⟩ := binary_first_order_polynomial_division P
  exact ⟨R, Q, by simpa only [hP, map_zero, zero_add] using h, hQ⟩

/-- The two original first derivatives show that an annihilator of u
modulo (u^2,P) must vanish at the origin when the transverse root is simple. -/
theorem binary_simple_root_coordinate_annihilator_vanishes
    (P : MvPolynomial (Fin 2) F) (hP : aeval (fun _ : Fin 2 => (0 : F)) P = 0)
    (hPv : aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 P) ≠ 0)
    (s : MvPolynomial (Fin 2) F)
    (hs : s * X 0 ∈ Ideal.span ({X 0 ^ 2, P} : Set (MvPolynomial (Fin 2) F))) :
    aeval (fun _ : Fin 2 => (0 : F)) s = 0 := by
  obtain ⟨p, q, hpq⟩ := Ideal.mem_span_pair.mp hs
  have hP0 : constantCoeff P = 0 := by simpa using hP
  have hPv0 : constantCoeff (pderiv 1 P) ≠ 0 := by simpa using hPv
  have h0 := congrArg (fun z : MvPolynomial (Fin 2) F => aeval (fun _ : Fin 2 => (0 : F)) (pderiv 0 z)) hpq
  have h1 := congrArg (fun z : MvPolynomial (Fin 2) F => aeval (fun _ : Fin 2 => (0 : F)) (pderiv 1 z)) hpq
  simp [pderiv_X, hP0] at h0 h1
  have hq : constantCoeff q = 0 := h1.resolve_right hPv0
  simpa [hq] using h0.symm

end DimensionFourDependence
