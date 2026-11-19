import DimensionFourDependence.LinearSubst
import DimensionFourDependence.ImageEquationWitness
import DimensionFourDependence.HomogeneousEvaluationScaling
import DimensionFourDependence.Nilpotent

/-! # The primitive part of a nonplanar image has degree at least two

Removing a common scalar factor preserves component independence.
Independent homogeneous linear forms give an injective polynomial
substitution, so they cannot satisfy the actual nonzero image equation.
Constant primitive coordinates are also excluded. Consequently the
primitive degree is at least two and the common factor has degree at
most the original degree minus two, as used in Section 4.2.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {K : Type*} [Field K] {n : ℕ}

/-- A relation among the scalar-free components lifts to the original
polynomial map with that common factor. -/
theorem componentsDependent_common_factor
    (P : Fin n → MvPolynomial (Fin n) K) (g : MvPolynomial (Fin n) K)
    (hP : ComponentsDependent P) : ComponentsDependent (fun i => g * P i) := by
  obtain ⟨c, hc, hrel⟩ := hP
  refine ⟨c, hc, ?_⟩
  calc
    _ = g * ∑ i, c i • P i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [MvPolynomial.smul_eq_C_mul]
      ring
    _ = 0 := by rw [hrel, mul_zero]

/-- Component independence is precisely the finite linear-independence
condition needed for the coordinate-space arguments. -/
theorem linearIndependent_of_componentsIndependent
    (P : Fin n → MvPolynomial (Fin n) K) (hP : ¬ ComponentsDependent P) :
    LinearIndependent K P := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hz : c = 0 := by
    by_contra hn
    exact hP ⟨c, hn, hc⟩
  exact congrFun hz i

/-- Four constant homogeneous coordinates cannot be independent. -/
theorem homogeneous_degree_zero_componentsDependent
    (P : Fin 4 → MvPolynomial (Fin 4) K) (hP : IsHomogMap P 0) : ComponentsDependent P := by
  by_contra hind
  have hLI := linearIndependent_of_componentsIndependent P hind
  have hscalar : LinearIndependent K (fun i => (P i).coeff 0) := by
    apply LinearIndependent.of_comp (Algebra.linearMap K (MvPolynomial (Fin 4) K))
    convert hLI using 1
    funext i
    exact (eq_C_of_isHomogeneous_zero (hP i)).symm
  have hbound := hscalar.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_self] at hbound
  omega

variable [CharZero K]

/-- Four independent homogeneous linear coordinate forms give an
injective substitution on their entire polynomial ring. -/
theorem homogeneous_linear_aeval_injective_of_componentsIndependent
    (P : Fin 4 → MvPolynomial (Fin 4) K) (hP : IsHomogMap P 1)
    (hind : ¬ ComponentsDependent P) : Function.Injective (aeval (R := K) P) := by
  let B : Matrix (Fin 4) (Fin 4) K := fun i j => (pderiv i (P j)).coeff 0
  have hcoord (j : Fin 4) : P j = ∑ i, C (B i j) * X i :=
    eq_sum_of_isHomogeneous_one (hP j)
  have hJ (i j : Fin 4) : (jac P) i j = C (B j i) :=
    eq_C_of_isHomogeneous_zero ((hP i).pderiv (i := j))
  rcases linear_dichotomy B with ⟨c, hc, hBc⟩ | ⟨D, hDB⟩
  · apply False.elim
    apply hind
    apply dependent_of_constant_left_kernel P (by norm_num) hP c hc
    funext j
    change (∑ i, C (c i) * (jac P) i j) = 0
    simp only [hJ, ← map_mul, ← map_sum]
    have he : (∑ i, c i * B j i) = 0 := by
      simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply, mul_comm] using congrFun hBc j
    rw [he, map_zero]
  · exact aeval_injective_of_mul_eq_one B D hDB P hcoord

/-- A nonplanar polynomial map with a genuine homogeneous image
equation cannot have scalar-free homogeneous degree zero or one. -/
theorem primitive_map_degree_ge_two_of_actual_image_relation
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hind : ¬ ComponentsDependent H)
    (I : ImageRelationWitness H) (g : MvPolynomial (Fin 4) K) (hg : g ≠ 0)
    (P : Fin 4 → MvPolynomial (Fin 4) K) {D : ℕ} (hP : IsHomogMap P D)
    (hHP : H = fun i => g * P i) : 2 ≤ D := by
  have hindP : ¬ ComponentsDependent P := by
    intro hp
    apply hind
    rw [hHP]
    exact componentsDependent_common_factor P g hp
  by_contra hn
  have hcases : D = 0 ∨ D = 1 := by omega
  rcases hcases with rfl | rfl
  · exact hindP (homogeneous_degree_zero_componentsDependent P hP)
  · have he : aeval (fun i => g * P i) I.equation = 0 :=
      (congrArg (fun V : Fin 4 → MvPolynomial (Fin 4) K => aeval V I.equation) hHP).symm.trans I.vanishing
    rw [homogeneous_aeval_scale I.equation I.homogeneous P g] at he
    have hrel : aeval P I.equation = 0 :=
      (mul_eq_zero.mp he).resolve_left (pow_ne_zero I.degree hg)
    apply I.irreducible.ne_zero
    apply homogeneous_linear_aeval_injective_of_componentsIndependent P hP hindP
    simpa only [map_zero] using hrel

/-- The original map supplies a primitive factorization with degree
at least two and common-factor degree at most `d - 2`. -/
theorem exists_primitive_factorization_common_degree_le_sub_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H) :
    ∃ (g : MvPolynomial (Fin 4) K) (P : Fin 4 → MvPolynomial (Fin 4) K) (c : ℕ),
      c ≤ d - 2 ∧ g ≠ 0 ∧ g.IsHomogeneous c ∧ IsHomogMap P (d - c) ∧
      IsPrimitiveVec P ∧ H = (fun i => g * P i) ∧ 2 ≤ d - c := by
  have hH0 : H ≠ 0 := by
    intro hz
    apply hind
    rw [hz]
    exact ⟨fun _ => 1, by simp [funext_iff], by simp⟩
  obtain ⟨g, P, c, hc, hg0, hgh, hP, hprim, hHP⟩ := exists_primitive_factorization d H hH hH0
  have hD := primitive_map_degree_ge_two_of_actual_image_relation H hind I g hg0 P hP hHP
  exact ⟨g, P, c, by omega, hg0, hgh, hP, hprim, hHP, hD⟩

end DimensionFourDependence
