import DimensionFourDependence.ClosedGaussHomogeneousParameter
import DimensionFourDependence.GaussPencilDegreeBound

/-! # The actual relatively closed Gauss pencil satisfies the degree bound -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

local notation "R" => MvPolynomial (Fin 4) K
local notation "F" => FractionRing (MvPolynomial (Fin 4) K)

/-- The pencil belonging to the relatively closed cover has degree at most
the primitive map degree. All coefficients come from the original map. -/
theorem actual_closed_gauss_parameter_pencil_degree_le_primitive_degree
    (H : Fin 4 → R) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
    (g : R) (hg : g ≠ 0) (P : Fin 4 → R) {D : ℕ} (hP : IsHomogMap P D)
    (hHP : H = fun i => g * P i) :
    ∃ p q : R, ∃ E : ℕ, 0 < E ∧ E ≤ D ∧ p ≠ 0 ∧ q ≠ 0 ∧
      p.IsHomogeneous E ∧ q.IsHomogeneous E ∧ IsRelPrime p q ∧
      closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q := by
  let f := closedGaussParameterSourceHom H I e
  let w := closedGaussParameterNormal H I e
  have ha : rationalImageNormal H I.equation (imageNormalPivot H I) ≠ 0 := imageNormalPivot_ne_zero H I
  have hw0 : w ≠ 0 := by
    intro hz
    have he := closedGaussParameterSourceHom_normal H I e (imageNormalPivot H I)
    change f (w (imageNormalPivot H I)) = _ at he
    rw [hz, Pi.zero_apply, map_zero, div_self ha] at he
    exact zero_ne_one he
  obtain ⟨v, hv, _, s, hs, hwrep⟩ := rational_vector_primitive_polynomial_presentation w hw0
  have hsF : f s ≠ 0 := by
    intro hz
    apply hs
    have he : f s = f 0 := by rw [hz, map_zero]
    exact f.injective he
  have hrep (i : Fin 4) : f (w i) = f s * Polynomial.aeval (f RatFunc.X) (v i) := by
    rw [hwrep i, map_mul, rational_function_algHom_polynomial_value]
  have hgF : algebraMap R F g ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hg
  have hHEuler := I.normalized_normal_dot_output_eq_zero H hd hH
  have hPEuler : (∑ i, f (w i) * algebraMap R F (P i)) = 0 := by
    have hh : algebraMap R F g * (∑ i, f (w i) * algebraMap R F (P i)) = 0 := by
      calc
        _ = (fun i => rationalImageNormal H I.equation i /
            rationalImageNormal H I.equation (imageNormalPivot H I)) ⬝ᵥ
            (fun i => algebraMap R F (H i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          dsimp only
          have hi : algebraMap R F (H i) = algebraMap R F g * algebraMap R F (P i) := by
            rw [congrFun hHP i, map_mul]
          rw [hi, show f (w i) = _ from closedGaussParameterSourceHom_normal H I e i]
          ring
        _ = 0 := hHEuler
    exact (mul_eq_zero.mp hh).resolve_left hgF
  have hsection : (∑ i, Polynomial.aeval (f RatFunc.X) (v i) * algebraMap R F (P i)) = 0 := by
    have hh : f s * (∑ i, Polynomial.aeval (f RatFunc.X) (v i) * algebraMap R F (P i)) = 0 := by
      rw [Finset.mul_sum]
      convert hPEuler using 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hrep]
      ring
    exact (mul_eq_zero.mp hh).resolve_left hsF
  have hindP : ¬ ComponentsDependent P := by
    intro hp
    apply hind
    rw [hHP]
    exact componentsDependent_common_factor P g hp
  obtain ⟨p, q, E, hE, hp, hq, hpH, hqH, hrel, he⟩ :=
    actual_closed_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  have hb : E ≤ D := homogeneous_pencil_degree_le_map_degree_of_parameter_relation p q hq hpH hqH hrel P hP
    (linearIndependent_of_componentsIndependent P hindP) v hv (by rw [← he]; exact hsection)
  exact ⟨p, q, E, hE, hb, hp, hq, hpH, hqH, hrel, he⟩

/-- The original map constructs the finite relatively closed rational
Gauss cover and its positive homogeneous pencil with both Section 4.2 bounds. -/
theorem exists_actual_closed_gauss_pencil_and_primitive_degree_bounds
    (H : Fin 4 → R) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ (g : R) (P : Fin 4 → R) (c : ℕ)
      (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (p q : R) (E : ℕ),
      c ≤ d - 2 ∧ g ≠ 0 ∧ g.IsHomogeneous c ∧ IsHomogMap P (d - c) ∧
      IsPrimitiveVec P ∧ H = (fun i => g * P i) ∧ 2 ≤ d - c ∧
      0 < E ∧ E ≤ d - c ∧ p ≠ 0 ∧ q ≠ 0 ∧
      p.IsHomogeneous E ∧ q.IsHomogeneous E ∧ IsRelPrime p q ∧
      closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q ∧
      IntermediateField.adjoin K {algebraMap R F p / algebraMap R F q} =
        closedGaussParameterField H I ∧
      algebraicClosure (closedGaussParameterField H I) F = ⊥ := by
  obtain ⟨g, P, c, hc, hg, hgh, hP, hprim, hHP, hD⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  obtain ⟨e⟩ := actual_closed_gauss_parameter_rational_function_field H I hGauss
  obtain ⟨p, q, E, hE, hED, hp, hq, hpH, hqH, hrel, he⟩ :=
    actual_closed_gauss_parameter_pencil_degree_le_primitive_degree H hd hH hind I e g hg P hP hHP
  refine ⟨g, P, c, e, p, q, E, hc, hg, hgh, hP, hprim, hHP, hD, hE, hED, hp, hq,
    hpH, hqH, hrel, he, ?_, closedGaussParameterField_relatively_closed H I⟩
  rw [← he]
  exact closedGaussParameterSourceHom_X_adjoin H I e

end DimensionFourDependence
