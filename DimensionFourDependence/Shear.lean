import DimensionFourDependence.Nilpotent

/-! # The inverse in Proposition 6.4

We work over an arbitrary commutative coefficient ring `R`. Taking
`R = K[z,t]` gives precisely the four-variable shear in (6.8) and (6.10).
The construction is an actual polynomial algebra automorphism.
The stable-tameness assertion is a separate obligation.
-/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 1000000

variable {R : Type*} [CommRing R]

/-- The invariant `S = ax + by`. -/
noncomputable def invariant (a b : R) : MvPolynomial (Fin 2) R :=
  C a * X 0 + C b * X 1

/-- The shear with point coordinates `(x+bf(S), y-af(S))`. -/
noncomputable def coordinates (a b : R) (f : Polynomial R) :
    Fin 2 → MvPolynomial (Fin 2) R :=
  ![X 0 + C b * Polynomial.aeval (invariant a b) f,
    X 1 - C a * Polynomial.aeval (invariant a b) f]

@[irreducible] noncomputable def substitution (a b : R) (f : Polynomial R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval (coordinates a b f)

theorem substitution_X (a b : R) (f : Polynomial R) (i : Fin 2) :
    substitution a b f (X i) = coordinates a b f i := by
  simp [substitution]

theorem substitution_C (a b : R) (f : Polynomial R) (c : R) :
    substitution a b f (C c) = C c := by
  simp [substitution]

theorem invariant_fixed (a b : R) (f : Polynomial R) :
    substitution a b f (invariant a b) = invariant a b := by
  simp [substitution, invariant, coordinates]
  ring

theorem parameter_fixed (a b : R) (f g : Polynomial R) :
    substitution a b f (Polynomial.aeval (invariant a b) g) =
      Polynomial.aeval (invariant a b) g := by
  rw [← Polynomial.aeval_algHom_apply, invariant_fixed]

/-- Substitutions add their invariant parameters. -/
theorem substitution_add (a b : R) (f g : Polynomial R) :
    (substitution a b f).comp (substitution a b g) = substitution a b (f + g) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, substitution_X]
  fin_cases i
  · change substitution a b f (X 0 + C b * Polynomial.aeval (invariant a b) g) =
      X 0 + C b * Polynomial.aeval (invariant a b) (f + g)
    rw [map_add (substitution a b f), map_mul (substitution a b f),
      parameter_fixed a b f g, substitution_X a b f 0,
      substitution_C a b f b, map_add (Polynomial.aeval (invariant a b))]
    change (X 0 + C b * Polynomial.aeval (invariant a b) f) +
      C b * Polynomial.aeval (invariant a b) g = _
    ring
  · change substitution a b f (X 1 - C a * Polynomial.aeval (invariant a b) g) =
      X 1 - C a * Polynomial.aeval (invariant a b) (f + g)
    rw [map_sub (substitution a b f), map_mul (substitution a b f),
      parameter_fixed a b f g, substitution_X a b f 1,
      substitution_C a b f a, map_add (Polynomial.aeval (invariant a b))]
    change (X 1 - C a * Polynomial.aeval (invariant a b) f) -
      C a * Polynomial.aeval (invariant a b) g = _
    ring

theorem substitution_zero (a b : R) : substitution a b 0 = AlgHom.id R _ := by
  ext i
  fin_cases i <;> simp [substitution, coordinates]

/-- The polynomial automorphism claimed in Proposition 6.4, with the explicit
inverse obtained by replacing `f` by `-f`. -/
noncomputable def automorphism (a b : R) (f : Polynomial R) :
    MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R :=
  AlgEquiv.ofAlgHom (substitution a b f) (substitution a b (-f))
    (by rw [substitution_add, add_neg_cancel, substitution_zero])
    (by rw [substitution_add, neg_add_cancel, substitution_zero])

theorem automorphism_inverse (a b : R) (f : Polynomial R) :
    (automorphism a b f).symm = automorphism a b (-f) := by
  ext i
  rfl

end DimensionFourDependence.Shear
