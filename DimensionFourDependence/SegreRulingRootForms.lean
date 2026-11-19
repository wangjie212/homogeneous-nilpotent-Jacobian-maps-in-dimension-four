import DimensionFourDependence.SegreRulingDirectionCalculus

/-! # Section 5.3: the actual Segre ruling constructs finite linear-root forms -/

namespace DimensionFourDependence

open Matrix

universe u
set_option maxHeartbeats 2000000

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F]

/-- A nonzero original radial pairing and an algebraic direction on
its actual Segre ruling construct the binary linear-root factorization.
All coefficients lie in one finite extension of the exact ruling field.
The selected direction is a zero of the transverse factor, and the dth
power identity retains the original radial pairing. -/
theorem segre_nonzero_radial_product_finite_linear_root_forms
    (p : RatFunc K →ₐ[K] F) (δ : Fin 3 → Derivation K F F) (Y b : Fin 3 → F)
    (hcoord : ∀ i j, δ i (Y j) = if j = i then 1 else 0)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (hY0 : Y 0 ≠ 0) (j : Fin 3) (hp : p RatFunc.X = Y j / Y 0)
    (hb : b ≠ 0) (hruling : b j = (Y j / Y 0) * b 0)
    (halg : ∀ i, IsAlgebraic p.fieldRange (b i)) (htr : Algebra.trdeg K F ≤ 3)
    {d : ℕ} (hd : 0 < d) (c : F) (hc0 : c ≠ 0)
    (hc : coordinateEuler Y δ c = (d : F)⁻¹ * c)
    (hHess : matrixBilinearPairing (derivationHessian δ (Y 0 * c)) b b = 0) :
    ∃ C : IntermediateField p.fieldRange F, Module.Finite p.fieldRange C ∧
      ∃ (m s : Fin 3 → C) (ρ : F), m ≠ 0 ∧ s ≠ 0 ∧ ρ ≠ 0 ∧
        Y 0 * c = ((fun i => (m i : F)) ⬝ᵥ Y) * ρ ∧
        ρ ^ d = (fun i => (s i : F)) ⬝ᵥ Y ∧ (fun i => (s i : F)) ⬝ᵥ b = 0 ∧
        coordinateEuler b δ ρ = 0 ∧
        (Y 0 * c) ^ d = ((fun i => (s i : F)) ⬝ᵥ Y) * ((fun i => (m i : F)) ⬝ᵥ Y) ^ d ∧
        ρ = (Y 0 * c) / ((fun i => (m i : F)) ⬝ᵥ Y) := by
  have htD : coordinateEuler b δ (p RatFunc.X) = 0 := by
    rw [hp]
    exact segre_ruling_direction_fixes_coordinate_ratio δ Y b hcoord hY0 j hruling
  have htE : coordinateEuler Y δ (p RatFunc.X) = 0 := by
    rw [hp]
    exact segre_output_euler_fixes_coordinate_ratio δ Y hcoord j
  have hsecond := segre_parameter_algebraic_ruling_zero_acceleration
    p δ Y b hcoord hY0 j hp hruling halg (Y 0 * c) hHess
  have hweight := segre_radial_product_euler_weight δ Y hcoord c (d : F)⁻¹ hc
  have hf : Y 0 * c ≠ 0 := mul_ne_zero hY0 hc0
  obtain ⟨C, hfinite, m, s, ρ, hm, hs, hρ, hfactor, hroot, hsv, hDρ⟩ :=
    parametric_weighted_function_finite_linear_root_forms p δ Y b hcoord hcomm hb halg htD htE
      htr hd (Y 0 * c) hf hsecond hweight
  have hmY : ((fun i => (m i : F)) ⬝ᵥ Y) ≠ 0 := by
    intro he
    rw [he, zero_mul] at hfactor
    exact hf hfactor
  refine ⟨C, hfinite, m, s, ρ, hm, hs, hρ, hfactor, hroot, hsv, hDρ, ?_, ?_⟩
  · rw [hfactor, mul_pow, hroot, mul_comm]
  · exact (eq_div_iff hmY).mpr (by rw [mul_comm]; exact hfactor.symm)

end DimensionFourDependence
