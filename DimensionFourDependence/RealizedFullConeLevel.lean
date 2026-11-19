import DimensionFourDependence.RealizedAffineFullCone

/-! # The full cone presentation constructs its actual constant normal level -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 1000000

universe u

variable {K E G : Type u} [Field K] [Field E] [Field G]
    [Algebra K E] [Algebra E G] [Algebra K G]

/-- Constant original outputs and the nonzero cone scale construct
the scalar value of the original normal linear form. All the same
cone coefficients and root are retained in the geometric constants. -/
theorem realized_full_cone_constructs_actual_constant_normal_level
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (g : closedGaussParameterField H I →ₐ[K] E) (z : Fin 4 → G) (d : ℕ)
    (hcone : RealizedAffineFixedVertexFullCone H I e g z d)
    (y : Fin 4 → E) (hout : ∀ i, aeval z (H i) = algebraMap E G (y i)) :
    let ν : Fin 3 → E := fun i => g (e (closedGaussParameterNormal H I e i.castSucc))
    ∃ (R : E) (V : Fin 3 → E) (a b ell : E), R ≠ 0 ∧ V ≠ 0 ∧ b ≠ 0 ∧
      (∀ i, IsAlgebraic g.fieldRange (V i)) ∧ IsAlgebraic g.fieldRange a ∧
      IsAlgebraic g.fieldRange b ∧
      (∀ i : Fin 3, y i.castSucc = V i * R ^ d) ∧
      y (Fin.last 3) = a * R ^ d + b * R ^ (d - 1) * ell ∧
      (∑ i : Fin 3, algebraMap E G (ν i) * z i.castSucc) = algebraMap E G ell ∧ ν ⬝ᵥ V = 0 := by
  classical
  let ν : Fin 3 → E := fun i => g (e (closedGaussParameterNormal H I e i.castSucc))
  let Λ : G := ∑ i : Fin 3, algebraMap E G (ν i) * z i.castSucc
  obtain ⟨R, V, a, b, hR, hV, hb, hValg, haalg, hbalg, hfirst, hlast, hinc⟩ := hcone
  let ell := (y (Fin.last 3) - a * R ^ d) / (b * R ^ (d - 1))
  have hden : b * R ^ (d - 1) ≠ 0 := mul_ne_zero hb (pow_ne_zero _ hR)
  have hdenG : algebraMap E G b * algebraMap E G R ^ (d - 1) ≠ 0 :=
    mul_ne_zero ((map_ne_zero (algebraMap E G)).mpr hb)
      (pow_ne_zero _ ((map_ne_zero (algebraMap E G)).mpr hR))
  have hlast' : algebraMap E G (y (Fin.last 3)) = algebraMap E G a * algebraMap E G R ^ d +
      algebraMap E G b * algebraMap E G R ^ (d - 1) * Λ := (hout _).symm.trans hlast
  have hlevel : Λ = algebraMap E G ell := by
    simp only [ell, map_div₀, map_sub, map_mul, map_pow]
    apply (eq_div_iff hdenG).mpr
    linear_combination -hlast'
  refine ⟨R, V, a, b, ell, hR, hV, hb, hValg, haalg, hbalg, ?_, ?_, hlevel, hinc⟩
  · intro i
    apply (algebraMap E G).injective
    simpa only [map_mul, map_pow] using (hout i.castSucc).symm.trans (hfirst i)
  · have he : ell * (b * R ^ (d - 1)) = y (Fin.last 3) - a * R ^ d :=
      div_mul_cancel₀ _ hden
    linear_combination -he

end DimensionFourDependence
