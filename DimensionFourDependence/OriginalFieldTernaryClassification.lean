import DimensionFourDependence.ClosedFieldTernaryNormalForm
import DimensionFourDependence.TernaryOuterFrameDescent
import DimensionFourDependence.TernaryOuterNormalizerFormula
import DimensionFourDependence.TernaryParabolicCoefficientDescent
import DimensionFourDependence.TernaryOriginalParabolicNormalForm
import DimensionFourDependence.TamenessFromTernaryClassification

/-! # The main tameness theorem over the original characteristic-zero field -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 4600000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "M₃" => Matrix (Fin 3) (Fin 3) K

omit [CharZero K] in
/-- An extension-field normalizer for an original map descends to an
original constant conjugacy and an original ordinary polynomial. -/
theorem ternary_normal_form_descends_from_field_extension
    {E : Type u} [Field E] [CharZero E] [Algebra K E]
    (H : Fin 3 → R₃) (T S : Matrix (Fin 3) (Fin 3) E) (hTS : T * S = 1) (hST : S * T = 1)
    (Q : Polynomial E) (hQ : 0 < Q.natDegree) (hQ₀ : Q.eval 0 = 0)
    (he : linearPolynomialConjugate T S (fun i => MvPolynomial.map (algebraMap K E) (H i)) =
      TernaryNormalForm.perturbation3 Q) :
    ∃ (A B : M₃) (P : Polynomial K), A * B = 1 ∧ B * A = 1 ∧ 0 < P.natDegree ∧ P.eval 0 = 0 ∧
      linearPolynomialConjugate A B H = TernaryNormalForm.perturbation3 P := by
  obtain ⟨t, a, b, ht, h₀, h₂⟩ := ternary_normalizing_outer_covectors_descend H T S hTS hST Q hQ he
  obtain ⟨A, B, U, V, hAB, hBA, hUV, _, hv₀, hv₂, hv⟩ :=
    ternary_extension_normalizer_reframes_with_original_outer_coordinates H T S hTS hST Q he t a b h₀ h₂
  let G := linearPolynomialConjugate B A H
  obtain ⟨lam, b₀, d₀, QE, hlam, hQE, hQE₀, hg₀, hg₁, hg₂⟩ :=
    ternary_outer_normalizer_constructs_original_output_formulas
      (fun i => MvPolynomial.map (algebraMap K E) (G i)) U V hUV Q hQ hQ₀ hv t ht hv₀ hv₂
  obtain ⟨μ, b₁, d₁, QK, hμ, hQK, hQK₀, hG₀, hG₁, hG₂⟩ :=
    ternary_parabolic_output_formulas_descend G lam b₀ d₀ hlam QE hQE hQE₀ hg₀ hg₁ hg₂
  obtain ⟨C, D, P, hCD, hDC, hP, hP₀, hPform⟩ :=
    ternary_parabolic_output_formula_conjugates_to_normal_form G μ b₁ d₁ hμ QK hQK hQK₀ hG₀ hG₁ hG₂
  refine ⟨B * C, D * A, P, ?_, ?_, hP, hP₀, ?_⟩
  · rw [Matrix.mul_assoc B C, ← Matrix.mul_assoc C D, hCD, Matrix.one_mul, hBA]
  · rw [Matrix.mul_assoc D A, ← Matrix.mul_assoc A B, hAB, Matrix.one_mul, hDC]
  · rw [← linearPolynomialConjugate_compose B A C D]
    exact hPform

/-- The cited classification in Theorem 6.1 over the original
characteristic-zero field. -/
theorem theorem_6_1 : TernaryNilpotentClassification K := by
  intro H h₀ hN hind
  let E := AlgebraicClosure K
  let f := algebraMap K E
  let G : Fin 3 → MvPolynomial (Fin 3) E := fun i => MvPolynomial.map f (H i)
  have hG₀ (i : Fin 3) : aeval (fun _ : Fin 3 => (0 : E)) (G i) = 0 := by
    let e : K →ₐ[K] E := Algebra.ofId K E
    have h := polynomial_aeval_scalar_extension (E := E) e (fun _ : Fin 3 => (0 : K)) (H i)
    have hz : e ∘ (fun _ : Fin 3 => (0 : K)) = fun _ : Fin 3 => (0 : E) := by
      funext j
      exact map_zero e
    rw [h₀ i, map_zero, hz] at h
    exact h.symm
  obtain ⟨T, S, P, hTS, hST, hP, hP₀, he⟩ := closed_field_ternary_nilpotent_classification
    G hG₀ (ternary_nilpotent_jacobian_scalar_extension H hN)
      (fun h => hind (componentsDependent_of_map E H h))
  exact ternary_normal_form_descends_from_field_extension H T S hTS hST P hP hP₀ he

/-- The exact original-field stable and degree-five tame statement
of Theorem 1.2 of the paper. -/
theorem theorem_1_2 : TamenessTheorem K := theorem_1_2_of_ternary_classification theorem_6_1

end DimensionFourDependence
