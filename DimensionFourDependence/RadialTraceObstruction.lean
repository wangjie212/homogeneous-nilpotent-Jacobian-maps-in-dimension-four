import DimensionFourDependence.RadialTraceIdentities

/-! # The radial fixed-point trace contradiction, including common powers

This is the polynomial version of (3.1)--(3.2), after multiplying the
local presentation by a source coordinate. The positive coefficient is
`e+2+m(n-1)` exactly as in the paper; exponent zero is included.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

/-- The normalized divergence remains zero after removing a common power. -/
theorem normalized_divergence_zero_of_power_factor
    (R S : MvPolynomial (Fin 4) K) (hR0 : R ≠ 0)
    (H V : Fin 4 → MvPolynomial (Fin 4) K) (m : ℕ)
    (hHV : H = fun i => R ^ m * V i)
    (hS : polynomialGradientPairing R V = R * S) (hdiv : divergence H = 0) :
    divergence V + m • S = 0 := by
  rw [hHV, polynomialDivergence_power_factor R S V hS m] at hdiv
  exact (mul_eq_zero.mp hdiv).resolve_left (pow_ne_zero m hR0)

/-- No trace-zero homogeneous presentation can fix the generic image
radially after removal of its maximal common image-equation power. -/
theorem no_radial_coordinate_presentation [CharZero K]
    (R : MvPolynomial (Fin 4) K) {n : ℕ} (hn : 0 < n)
    (hRh : R.IsHomogeneous n) (hR : Irreducible R)
    (H V W : Fin 4 → MvPolynomial (Fin 4) K) {e : ℕ} (hVh : IsHomogMap V e)
    (m : ℕ) (hHV : H = fun i => R ^ m * V i)
    (hV : aeval V R = 0) (hdiv : divergence H = 0) (j : Fin 4)
    (hq : ¬ R ∣ X j) (hf : ¬ R ∣ V j)
    (hpoint : (fun i => X j * V i) = fun i => V j * X i + R * W i) : False := by
  obtain ⟨S, hS, hqS⟩ := radial_presentation_gradient_factor R (X j) (V j) hRh hR hq V W hpoint
  obtain ⟨T, hT⟩ := radial_taylor_gradient_congruence R (V j) (X j) hn hRh hR hf V W hV hpoint
  have hD := radial_coordinate_presentation_divergence R V W hVh j hpoint
  have hN := normalized_divergence_zero_of_power_factor R S hR.ne_zero H V m hHV hS hdiv
  have hncast : (n : MvPolynomial (Fin 4) K) = ((n - 1 : ℕ) : MvPolynomial (Fin 4) K) + 1 := by
    have he : n = (n - 1) + 1 := by omega
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun a : ℕ => (a : MvPolynomial (Fin 4) K)) he
  have hcoef : R ∣ ((e + 2 + m * (n - 1) : ℕ) : MvPolynomial (Fin 4) K) * V j := by
    refine ⟨-(((m : MvPolynomial (Fin 4) K) + 1) * T + divergence W), ?_⟩
    rw [hncast] at hqS
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hD hN ⊢
    linear_combination -hD - (m : MvPolynomial (Fin 4) K) * hqS -
      ((m : MvPolynomial (Fin 4) K) + 1) * hT + X j * hN
  have hconstant : R ∣ ((e + 2 + m * (n - 1) : ℕ) : MvPolynomial (Fin 4) K) :=
    (hR.prime.dvd_or_dvd hcoef).resolve_right hf
  have hunit : IsUnit ((e + 2 + m * (n - 1) : ℕ) : MvPolynomial (Fin 4) K) := by
    change IsUnit (C ((e + 2 + m * (n - 1) : ℕ) : K))
    apply IsUnit.map C
    exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
  exact hR.not_isUnit (isUnit_of_dvd_unit hconstant hunit)

end DimensionFourDependence
