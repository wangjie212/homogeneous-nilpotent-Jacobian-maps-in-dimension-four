import DimensionFourDependence.QuadraticParameterNonconstancy

/-! # Nonconstant parameters in the zero-radial quadratic normal form

On `q=kappa*s*t` with nonzero `q,kappa`, a scalar parameter makes
both parameters scalar. The full source coordinates then lie on the
radial affine line, regardless of the remaining radial parameter.
-/

namespace DimensionFourDependence

variable {E F : Type*} [Field E] [Field F] [Algebra E F] {n : ℕ}

/-- A scalar coordinate on a nondegenerate hyperbola makes the other
coordinate scalar as well. -/
theorem hyperbola_scalar_parameter_partner
    (κ q : E) (hκ : κ ≠ 0) (hq : q ≠ 0) (s t : F)
    (heq : algebraMap E F q = algebraMap E F κ * s * t)
    (hs : ∃ e : E, algebraMap E F e = s) :
    ∃ e : E, algebraMap E F e = t := by
  obtain ⟨s₀, hs₀⟩ := hs
  have hs0 : s₀ ≠ 0 := by
    intro hz
    have he : algebraMap E F q = 0 := by
      simpa only [← hs₀, hz, map_zero, mul_zero, zero_mul] using heq
    exact hq ((algebraMap E F).injective (by simpa only [map_zero] using he))
  have hκF : algebraMap E F κ ≠ 0 := by
    simpa only [map_zero] using (algebraMap E F).injective.ne hκ
  have hsF : algebraMap E F s₀ ≠ 0 := by
    simpa only [map_zero] using (algebraMap E F).injective.ne hs0
  refine ⟨q / (κ * s₀), ?_⟩
  rw [map_div₀, map_mul, div_eq_iff (mul_ne_zero hκF hsF)]
  rw [heq, hs₀]
  ring

/-- One scalar isotropic parameter in the hyperbola normal form
forces affine-line containment of the entire full-coordinate fiber. -/
theorem hyperbola_scalar_parameter_liesInAffineLine
    (x : Fin n → F) (Y Z W c : Fin n → E) (τ s t : F) (κ q : E)
    (hκ : κ ≠ 0) (hq : q ≠ 0)
    (hx : ∀ i, x i = τ * algebraMap E F (Y i) + s * algebraMap E F (Z i) +
      t * algebraMap E F (W i) + algebraMap E F (c i))
    (heq : algebraMap E F q = algebraMap E F κ * s * t)
    (hs : ∃ e : E, algebraMap E F e = s) (j : Fin n) : LiesInAffineLine (E := E) x := by
  obtain ⟨t₀, ht₀⟩ := hyperbola_scalar_parameter_partner κ q hκ hq s t heq hs
  obtain ⟨s₀, hs₀⟩ := hs
  apply liesInAffineLine_of_affine_parameterization x
    (fun i => s₀ * Z i + t₀ * W i + c i) Y τ _ j
  intro i
  rw [hx i, ← hs₀, ← ht₀]
  simp only [map_add, map_mul]
  ring

/-- Nonlinearity on the hyperbola normal form supplies two nonscalar
parameters, without any extra hypothesis about the cubic graph. -/
theorem nonlinear_hyperbola_parameters_nonscalar
    (x : Fin n → F) (Y Z W c : Fin n → E) (τ s t : F) (κ q : E)
    (hκ : κ ≠ 0) (hq : q ≠ 0)
    (hx : ∀ i, x i = τ * algebraMap E F (Y i) + s * algebraMap E F (Z i) +
      t * algebraMap E F (W i) + algebraMap E F (c i))
    (heq : algebraMap E F q = algebraMap E F κ * s * t)
    (hline : ¬ LiesInAffineLine (E := E) x) (j : Fin n) :
    (¬ ∃ e : E, algebraMap E F e = s) ∧ (¬ ∃ e : E, algebraMap E F e = t) := by
  refine ⟨fun hs => hline (hyperbola_scalar_parameter_liesInAffineLine
    x Y Z W c τ s t κ q hκ hq hx heq hs j), ?_⟩
  intro ht
  apply hline
  apply hyperbola_scalar_parameter_liesInAffineLine x Y W Z c τ t s κ q hκ hq
    (fun i => by rw [hx i]; ring) _ ht j
  linear_combination heq

end DimensionFourDependence
