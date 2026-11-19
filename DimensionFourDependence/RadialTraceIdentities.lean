import DimensionFourDependence.RadialTaylorCongruence

/-! # Exact identities underlying the radial fixed-point trace congruence -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

/-- Pair the cleared radial presentation with the image gradient. -/
theorem radial_presentation_gradient_identity
    (R q f : MvPolynomial (Fin 4) K) {n : ℕ} (hRh : R.IsHomogeneous n)
    (V W : Fin 4 → MvPolynomial (Fin 4) K)
    (hpoint : (fun i => q * V i) = fun i => f * X i + R * W i) :
    q * polynomialGradientPairing R V = R * ((n : MvPolynomial (Fin 4) K) * f +
      polynomialGradientPairing R W) := by
  have hsum : (fun i : Fin 4 => q * V i) =
      (fun i : Fin 4 => f * X i) + (fun i : Fin 4 => R * W i) := hpoint
  have he := congrArg (polynomialGradientPairing R) hsum
  rw [polynomialGradientPairing_scalar, polynomialGradientPairing_add,
    polynomialGradientPairing_scalar, polynomialGradientPairing_scalar,
    polynomialGradientPairing_radial R hRh] at he
  simp only [nsmul_eq_mul] at he
  linear_combination he

/-- Primality and a nonvanishing denominator produce the exact quotient
of the image-gradient pairing by the image equation. -/
theorem radial_presentation_gradient_factor
    (R q f : MvPolynomial (Fin 4) K) {n : ℕ} (hRh : R.IsHomogeneous n)
    (hR : Irreducible R) (hq : ¬ R ∣ q) (V W : Fin 4 → MvPolynomial (Fin 4) K)
    (hpoint : (fun i => q * V i) = fun i => f * X i + R * W i) :
    ∃ S : MvPolynomial (Fin 4) K,
      polynomialGradientPairing R V = R * S ∧
      q * S = (n : MvPolynomial (Fin 4) K) * f + polynomialGradientPairing R W := by
  have he := radial_presentation_gradient_identity R q f hRh V W hpoint
  have hdiv : R ∣ q * polynomialGradientPairing R V := ⟨_, he⟩
  obtain ⟨S, hS⟩ := (hR.prime.dvd_or_dvd hdiv).resolve_left hq
  refine ⟨S, hS, ?_⟩
  apply mul_left_cancel₀ hR.ne_zero
  rw [hS] at he
  linear_combination he

/-- The divergence identity with a coordinate denominator and numerator
equal to the corresponding component of `V`. -/
theorem radial_coordinate_presentation_divergence
    (R : MvPolynomial (Fin 4) K) (V W : Fin 4 → MvPolynomial (Fin 4) K)
    {e : ℕ} (hVh : IsHomogMap V e) (j : Fin 4)
    (hpoint : (fun i => X j * V i) = fun i => V j * X i + R * W i) :
    X j * divergence V = (((e + 3 : ℕ) : MvPolynomial (Fin 4) K) * V j) +
      polynomialGradientPairing R W + R * divergence W := by
  have hsum : (fun i : Fin 4 => X j * V i) =
      (fun i : Fin 4 => V j * X i) + (fun i : Fin 4 => R * W i) := hpoint
  have he := congrArg (fun Z : Fin 4 → MvPolynomial (Fin 4) K => divergence Z) hsum
  rw [polynomialDivergence_coordinate, polynomialDivergence_add,
    polynomialDivergence_radial_four (V j) (hVh j), polynomialDivergence_scalar] at he
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat] at he ⊢
  linear_combination he

end DimensionFourDependence
