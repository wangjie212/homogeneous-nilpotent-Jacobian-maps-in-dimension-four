import DimensionFourDependence.ThreeSkewLineQuadric

/-! # Uniqueness of the quadric through three skew lines

An alternating bilinear form in two coordinates is a scalar determinant.
Polarization then proves that a quadratic form vanishing on both axes and
the diagonal is a scalar multiple of the standard ruling quadric.
-/

namespace DimensionFourDependence

variable {F : Type*} [Field F]

/-- An alternating bilinear form on a two-dimensional space is a scalar determinant. -/
theorem alternating_bilinear_two_coordinates
    (B : (Fin 2 → F) →ₗ[F] ((Fin 2 → F) →ₗ[F] F))
    (hB : ∀ a, B a a = 0) :
    ∃ d : F, ∀ a b, B a b = d * (a 0 * b 1 - a 1 * b 0) := by
  let e0 : Fin 2 → F := ![1, 0]
  let e1 : Fin 2 → F := ![0, 1]
  have h00 := hB e0
  have h11 := hB e1
  have h10 : B e1 e0 = -B e0 e1 := by
    have hsum := hB (e0 + e1)
    simp only [map_add, LinearMap.add_apply] at hsum
    rw [h00, h11] at hsum
    linear_combination hsum
  have hdecomp (a : Fin 2 → F) : a = a 0 • e0 + a 1 • e1 := by
    ext i
    fin_cases i <;> simp [e0, e1]
  refine ⟨B e0 e1, ?_⟩
  intro a b
  calc
    B a b = a 0 * b 0 * B e0 e0 + a 0 * b 1 * B e0 e1 +
        a 1 * b 0 * B e1 e0 + a 1 * b 1 * B e1 e1 := by
      conv_lhs => rw [hdecomp a, hdecomp b]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    _ = B e0 e1 * (a 0 * b 1 - a 1 * b 0) := by rw [h00, h11, h10]; ring

/-- Every quadratic form through the two axes and diagonal is a scalar determinant. -/
theorem quadratic_form_vanishing_on_three_standard_lines
    (Q : QuadraticForm F ((Fin 2 → F) × (Fin 2 → F)))
    (hfirst : ∀ a : Fin 2 → F, Q (a, 0) = 0)
    (hsecond : ∀ a : Fin 2 → F, Q (0, a) = 0)
    (hdiagonal : ∀ a : Fin 2 → F, Q (a, a) = 0) :
    ∃ d : F, ∀ x, Q x = d * standardRulingQuadric x := by
  let B : (Fin 2 → F) →ₗ[F] ((Fin 2 → F) →ₗ[F] F) :=
    Q.polarBilin.compl₁₂ (LinearMap.inl F _ _) (LinearMap.inr F _ _)
  have hQB (a b : Fin 2 → F) : Q (a, b) = B a b := by
    change Q (a, b) = Q (a + 0, 0 + b) - Q (a, 0) - Q (0, b)
    rw [hfirst, hsecond]
    simp
  have hB (a : Fin 2 → F) : B a a = 0 := (hQB a a).symm.trans (hdiagonal a)
  obtain ⟨d, hd⟩ := alternating_bilinear_two_coordinates B hB
  refine ⟨d, ?_⟩
  rintro ⟨a, b⟩
  exact (hQB a b).trans (hd a b)

/-- The determinant function is itself a quadratic form. -/
noncomputable def standardRulingQuadraticForm :
    QuadraticForm F ((Fin 2 → F) × (Fin 2 → F)) :=
  QuadraticMap.linMulLin
    ((LinearMap.proj 0).comp (LinearMap.fst F _ _))
    ((LinearMap.proj 1).comp (LinearMap.snd F _ _)) -
  QuadraticMap.linMulLin
    ((LinearMap.proj 1).comp (LinearMap.fst F _ _))
    ((LinearMap.proj 0).comp (LinearMap.snd F _ _))

/-- The quadratic form has the stated determinant value. -/
theorem standardRulingQuadraticForm_apply (x : (Fin 2 → F) × (Fin 2 → F)) :
    standardRulingQuadraticForm x = standardRulingQuadric x := rfl

/-- The space of quadratic forms through the standard three lines is one-dimensional,
expressed without any choice of polynomial representatives. -/
theorem quadratic_form_three_standard_lines_iff
    (Q : QuadraticForm F ((Fin 2 → F) × (Fin 2 → F))) :
    ((∀ a : Fin 2 → F, Q (a, 0) = 0) ∧ (∀ a : Fin 2 → F, Q (0, a) = 0) ∧
      (∀ a : Fin 2 → F, Q (a, a) = 0)) ↔
      ∃ d : F, Q = d • standardRulingQuadraticForm := by
  constructor
  · rintro ⟨hfirst, hsecond, hdiagonal⟩
    obtain ⟨d, hd⟩ := quadratic_form_vanishing_on_three_standard_lines Q hfirst hsecond hdiagonal
    refine ⟨d, ?_⟩
    ext x
    exact hd x
  · rintro ⟨d, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;> intro a <;>
      simp [standardRulingQuadraticForm_apply, standardRulingQuadric, mul_comm]

end DimensionFourDependence
