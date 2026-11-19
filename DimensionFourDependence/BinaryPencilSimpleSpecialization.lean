import DimensionFourDependence.SimpleRootSplitsBinaryQuadratic
import Mathlib.Algebra.Polynomial.Roots

/-! # A binary quadratic pencil has an original-field member with a simple root -/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The leading minors enforce the degree and simple-root conditions for
the pencil member obtained by canceling the values at the chosen root. -/
theorem binary_pencil_simple_affine_specialization
    (a₂ a₁ a₀ b₂ b₁ b₀ : K)
    (hminor : b₁ * a₂ - a₁ * b₂ ≠ 0 ∨ b₀ * a₂ - a₀ * b₂ ≠ 0) :
    ∃ r : K,
      let a := a₂ * r ^ 2 + a₁ * r + a₀
      let b := b₂ * r ^ 2 + b₁ * r + b₀
      b * a₂ - a * b₂ ≠ 0 ∧
        2 * (b * a₂ - a * b₂) * r + (b * a₁ - a * b₁) ≠ 0 := by
  let p := b₁ * a₂ - a₁ * b₂
  let q := b₀ * a₂ - a₀ * b₂
  let k := b₀ * a₁ - a₀ * b₁
  let P : Polynomial K := Polynomial.C p * Polynomial.X + Polynomial.C q
  let Q : Polynomial K :=
    Polynomial.C p * Polynomial.X ^ 2 + Polynomial.C (2 * q) * Polynomial.X + Polynomial.C k
  have hP : P ≠ 0 := by
    intro hz
    have h₁ := congrArg (fun f : Polynomial K => f.coeff 1) hz
    have h₀ := congrArg (fun f : Polynomial K => f.coeff 0) hz
    have hp : p = 0 := by simpa [P, Polynomial.coeff_C_mul_X] using h₁
    have hq : q = 0 := by simpa [P, Polynomial.coeff_C_mul_X] using h₀
    exact hminor.elim (fun h => h hp) (fun h => h hq)
  have hQ : Q ≠ 0 := by
    intro hz
    have h₂ := congrArg (fun f : Polynomial K => f.coeff 2) hz
    have h₁ := congrArg (fun f : Polynomial K => f.coeff 1) hz
    have hp : p = 0 := by simpa [Q, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X] using h₂
    have hq₂ : 2 * q = 0 := by
      simpa [Q, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X] using h₁
    have hq := (mul_eq_zero.mp hq₂).resolve_left two_ne_zero
    exact hminor.elim (fun h => h hp) (fun h => h hq)
  have h := mul_ne_zero hP hQ
  have hr : ∃ r, (P * Q).eval r ≠ 0 := by
    by_contra! hh
    apply h
    exact Polynomial.funext fun r => by simpa using hh r
  obtain ⟨r, hr⟩ := hr
  rw [Polynomial.eval_mul] at hr
  have hPr : P.eval r ≠ 0 := fun he => hr (by rw [he, zero_mul])
  have hQr : Q.eval r ≠ 0 := fun he => hr (by rw [he, mul_zero])
  let a := a₂ * r ^ 2 + a₁ * r + a₀
  let b := b₂ * r ^ 2 + b₁ * r + b₀
  have hlead : b * a₂ - a * b₂ = P.eval r := by
    simp [P, a, b, p, q]
    ring
  have hderiv : 2 * (b * a₂ - a * b₂) * r + (b * a₁ - a * b₁) = Q.eval r := by
    simp [Q, a, b, p, q, k]
    ring
  exact ⟨r, hlead ▸ hPr, hderiv ▸ hQr⟩

end DimensionFourDependence.Shear
