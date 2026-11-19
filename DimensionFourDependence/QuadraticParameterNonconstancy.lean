import DimensionFourDependence.GenericFiberCubicIsotropy

/-! # Nonlinearity makes both quadratic normal-form parameters nonscalar

When the radial coefficient in (3.3) is nonzero, a constant `s` or `t`
makes `tau` affine-linear in the other parameter and the whole fiber lies
on an affine line. Thus a nonlinear component supplies both poles.
-/

namespace DimensionFourDependence

variable {E F : Type*} [Field E] [Field F] [Algebra E F] {n : ℕ}

/-- An affine parametrization lies on a line, including a constant
parametrization whose displayed direction vector happens to vanish. -/
theorem liesInAffineLine_of_affine_parameterization
    (x : Fin n → F) (a v : Fin n → E) (t : F)
    (hx : ∀ i, x i = algebraMap E F (a i) + algebraMap E F (v i) * t) (j : Fin n) :
    LiesInAffineLine (E := E) x := by
  classical
  by_cases hv : v = 0
  · let w : Fin n → E := Pi.single j 1
    have hw : w ≠ 0 := by
      intro hz
      have he := congrFun hz j
      exact one_ne_zero (by simpa only [w, Pi.single_eq_same, Pi.zero_apply] using he)
    refine ⟨a, w, hw, 0, ?_⟩
    intro i
    simpa only [hv, Pi.zero_apply, map_zero, zero_mul, mul_zero, add_zero] using hx i
  · exact ⟨a, v, hv, t, hx⟩

/-- A scalar `s` in the nonzero-radial quadratic normal form forces the
entire full-coordinate parametrization to lie on an actual affine line. -/
theorem quadratic_normal_form_scalar_parameter_liesInAffineLine
    (x : Fin n → F) (Y Z W c : Fin n → E) (τ s t : F) (a α β κ q : E) (ha : a ≠ 0)
    (hx : ∀ i, x i = τ * algebraMap E F (Y i) + s * algebraMap E F (Z i) +
      t * algebraMap E F (W i) + algebraMap E F (c i))
    (heq : algebraMap E F q = algebraMap E F a * τ + algebraMap E F α * s +
      algebraMap E F β * t + algebraMap E F κ * s * t)
    (hs : ∃ e : E, algebraMap E F e = s) (j : Fin n) : LiesInAffineLine (E := E) x := by
  obtain ⟨s₀, hs₀⟩ := hs
  rw [← hs₀] at hx heq
  have haF : algebraMap E F a ≠ 0 := by
    intro hz
    exact ha ((algebraMap E F).injective (by simpa only [map_zero] using hz))
  let A : E := (q - α * s₀) / a
  let B : E := -(β + κ * s₀) / a
  have hτ : τ = algebraMap E F A + algebraMap E F B * t := by
    dsimp only [A, B]
    simp only [map_div₀, map_sub, map_mul, map_neg, map_add]
    field_simp [haF]
    linear_combination -heq
  let a₀ : Fin n → E := fun i => A * Y i + s₀ * Z i + c i
  let v : Fin n → E := fun i => B * Y i + W i
  apply liesInAffineLine_of_affine_parameterization x a₀ v t _ j
  intro i
  rw [hx i, hτ]
  simp only [a₀, v, map_add, map_mul]
  ring

/-- A nonlinear component in (3.3) has two nonscalar isotropic parameters. -/
theorem nonlinear_quadratic_normal_form_parameters_nonscalar
    (x : Fin n → F) (Y Z W c : Fin n → E) (τ s t : F) (a α β κ q : E) (ha : a ≠ 0)
    (hx : ∀ i, x i = τ * algebraMap E F (Y i) + s * algebraMap E F (Z i) +
      t * algebraMap E F (W i) + algebraMap E F (c i))
    (heq : algebraMap E F q = algebraMap E F a * τ + algebraMap E F α * s +
      algebraMap E F β * t + algebraMap E F κ * s * t)
    (hline : ¬ LiesInAffineLine (E := E) x) (j : Fin n) :
    (¬ ∃ e : E, algebraMap E F e = s) ∧ (¬ ∃ e : E, algebraMap E F e = t) := by
  refine ⟨fun hs => hline (quadratic_normal_form_scalar_parameter_liesInAffineLine
    x Y Z W c τ s t a α β κ q ha hx heq hs j), ?_⟩
  intro ht
  apply hline
  apply quadratic_normal_form_scalar_parameter_liesInAffineLine x Y W Z c τ t s a β α κ q ha
    (fun i => by rw [hx i]; ring) _ ht j
  linear_combination heq

end DimensionFourDependence
