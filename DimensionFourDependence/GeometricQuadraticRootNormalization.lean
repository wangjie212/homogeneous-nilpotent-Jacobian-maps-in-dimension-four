import DimensionFourDependence.ConeQuadraticRootNormalization

/-! # The constructed numerator and normalized root lie in the actual geometric constants -/

namespace DimensionFourDependence

variable {J E F : Type*} [Field J] [Field E] [Field F] [Algebra J F] [Algebra E F]

/-- If the actual parabolic coefficient and root are geometric
constants, the constructed nonzero numerator is a geometric constant
as well. Its parameter algebraicity is retained and C is nonzero. -/
theorem actual_quadratic_coefficient_numerator_descends_to_constants
    (C R : E) (κ : F) (hR : R ≠ 0) (hκ : κ ≠ 0) (hκalg : IsAlgebraic J κ)
    (hC : algebraMap E F C = κ / algebraMap E F R) :
    C ≠ 0 ∧ ∃ κ₀ : E, κ₀ ≠ 0 ∧ IsAlgebraic J (algebraMap E F κ₀) ∧
      C = κ₀ / R ∧ algebraMap E F κ₀ = κ := by
  have hRF : algebraMap E F R ≠ 0 := by simpa only [map_zero] using (algebraMap E F).injective.ne hR
  have he : algebraMap E F (C * R) = κ := by
    rw [map_mul, hC, div_mul_cancel₀ _ hRF]
  have hCR : C * R ≠ 0 := by
    intro hz
    apply hκ
    rw [← he, hz, map_zero]
  refine ⟨(mul_ne_zero_iff.mp hCR).1, C * R, hCR, ?_, ?_, he⟩
  · rw [he]; exact hκalg
  · exact (mul_div_cancel_right₀ C hR).symm

/-- The actual geometric root can be rescaled inside the constant
field so C = 1/R_new. All four cone formulas, parameter algebraicity
and the nonzero last coefficient survive in the same source field. -/
theorem actual_constant_cone_root_normalizes_quadratic_coefficient
    (C R : E) (κ a b L : F) (V : Fin 3 → F) (d : ℕ)
    (hR : R ≠ 0) (hκ : κ ≠ 0) (hb0 : b ≠ 0)
    (hC : algebraMap E F C = κ / algebraMap E F R)
    (hV : ∀ i, IsAlgebraic J (V i)) (ha : IsAlgebraic J a)
    (hb : IsAlgebraic J b) (hκalg : IsAlgebraic J κ) :
    C ≠ 0 ∧ ∃ (Rnew : E) (Vnew : Fin 3 → F) (anew bnew : F),
      Rnew ≠ 0 ∧ C = 1 / Rnew ∧ bnew ≠ 0 ∧
      (∀ i, IsAlgebraic J (Vnew i)) ∧ IsAlgebraic J anew ∧ IsAlgebraic J bnew ∧
      (∀ i : Fin 3, V i * (algebraMap E F R) ^ d = Vnew i * (algebraMap E F Rnew) ^ d) ∧
      a * (algebraMap E F R) ^ d + b * (algebraMap E F R) ^ (d - 1) * L =
        anew * (algebraMap E F Rnew) ^ d + bnew * (algebraMap E F Rnew) ^ (d - 1) * L := by
  obtain ⟨hC0, κ₀, hκ₀, hκ₀alg, hC₀, he⟩ :=
    actual_quadratic_coefficient_numerator_descends_to_constants C R κ hR hκ hκalg hC
  have hκF : algebraMap E F κ₀ ≠ 0 := by simpa only [map_zero] using (algebraMap E F).injective.ne hκ₀
  have hnorm := cone_root_rescaling_normalizes_quadratic_coefficient
    (algebraMap E F R) (algebraMap E F κ₀) (algebraMap E F C) a b L V d
    (by simpa only [map_zero] using (algebraMap E F).injective.ne hR) hκF (by rw [he]; exact hC)
  have halg := cone_root_rescaling_preserves_algebraic_coefficients V a b (algebraMap E F κ₀) d
    hV ha hb hκ₀alg
  refine ⟨hC0, R / κ₀, (fun i => V i * (algebraMap E F κ₀) ^ d),
    a * (algebraMap E F κ₀) ^ d, b * (algebraMap E F κ₀) ^ (d - 1),
    div_ne_zero hR hκ₀, ?_, hnorm.2.2.2.2 hb0, halg.1, halg.2.1, halg.2.2, ?_, ?_⟩
  · rw [hC₀]
    field_simp [hR, hκ₀]
  · simpa only [map_div₀] using hnorm.2.2.1
  · simpa only [map_div₀] using hnorm.2.2.2.1

end DimensionFourDependence
