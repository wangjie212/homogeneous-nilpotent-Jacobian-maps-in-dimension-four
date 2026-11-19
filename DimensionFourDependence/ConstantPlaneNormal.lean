import DimensionFourDependence.HomogeneousDifferentialDependence

/-! # The constant-plane normal criterion of Proposition 2.3

If a nonzero polynomial left normal lies in the span of two independent
constant covectors, the corresponding two constant combinations of the
outputs have dependent differentials. Homogeneity supplies a constant
relation among the original outputs.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] {n m : ℕ} {σ : Type*}

/-- A constant linear combination of the output polynomials. -/
noncomputable def outputLinearCombination (H : Fin m → MvPolynomial σ K) (v : Fin m → K) :
    MvPolynomial σ K := ∑ i, C (v i) * H i

theorem outputLinearCombination_homogeneous (H : Fin m → MvPolynomial σ K)
    {d : ℕ} (hH : IsHomogMap H d) (v : Fin m → K) :
    (outputLinearCombination H v).IsHomogeneous d :=
  IsHomogeneous.sum _ _ _ fun i _ => (hH i).C_mul (v i)

/-- A nontrivial relation between two independent constant combinations
gives a nontrivial relation among the original components. -/
theorem componentsDependent_of_independent_output_combinations
    (H : Fin m → MvPolynomial σ K) (v w : Fin m → K)
    (hvw : LinearIndependent K ![v, w]) (c t : K) (hct : c ≠ 0 ∨ t ≠ 0)
    (hrel : c • outputLinearCombination H v + t • outputLinearCombination H w = 0) :
    ComponentsDependent H := by
  refine ⟨c • v + t • w, ?_, ?_⟩
  · intro hz
    have he := Fintype.linearIndependent_iff.mp hvw ![c, t] (by simpa using hz)
    have hc : c = 0 := by simpa using he 0
    have ht : t = 0 := by simpa using he 1
    exact hct.elim (fun h => h hc) (fun h => h ht)
  · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, ← Finset.smul_sum, outputLinearCombination,
      MvPolynomial.smul_eq_C_mul, Finset.mul_sum] using hrel

/-- The algebraic dependence conclusion after the fixed annihilated
two-space reduction in Proposition 2.3; no geometric classification is assumed. -/
theorem dependent_of_left_normal_in_constant_plane [CharZero K]
    (H : Fin n → MvPolynomial (Fin n) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (v w : Fin n → K) (hvw : LinearIndependent K ![v, w])
    (a b : MvPolynomial (Fin n) K) (hab : a ≠ 0 ∨ b ≠ 0)
    (hker : (fun i => a * C (v i) + b * C (w i)) ᵥ* jac H = 0) :
    ComponentsDependent H := by
  have hgrad (k : Fin n) :
      a * pderiv k (outputLinearCombination H v) +
        b * pderiv k (outputLinearCombination H w) = 0 := by
    have hk := congrFun hker k
    change (∑ i, (a * C (v i) + b * C (w i)) * pderiv k (H i)) = 0 at hk
    simpa [outputLinearCombination, map_sum, Derivation.leibniz,
      Finset.mul_sum, Finset.sum_add_distrib, add_mul, mul_assoc] using hk
  obtain ⟨c, t, hct, hrel⟩ := constant_relation_of_homogeneous_differential_relation
    (outputLinearCombination H v) (outputLinearCombination H w) a b hd
    (outputLinearCombination_homogeneous H hH v)
    (outputLinearCombination_homogeneous H hH w) hab hgrad
  exact componentsDependent_of_independent_output_combinations H v w hvw c t hct hrel

/-- Apply the constant-plane criterion to the actual normal constructed
from the irreducible image relation. The geometric reduction to such a
constant plane is the remaining input of Proposition 2.3. -/
theorem ImageRelationWitness.dependent_of_normal_in_constant_plane [CharZero K]
    (H : Fin n → MvPolynomial (Fin n) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (W : ImageRelationWitness H) (v w : Fin n → K) (hvw : LinearIndependent K ![v, w])
    (a b : MvPolynomial (Fin n) K)
    (he : imageRelationNormal H W.equation = fun i => a * C (v i) + b * C (w i)) :
    ComponentsDependent H := by
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hn
    push Not at hn
    apply W.normal_ne_zero
    rw [he, hn.1, hn.2]
    funext i
    simp
  apply dependent_of_left_normal_in_constant_plane H hd hH v w hvw a b hab
  rw [← he]
  exact W.left_kernel H

end DimensionFourDependence
