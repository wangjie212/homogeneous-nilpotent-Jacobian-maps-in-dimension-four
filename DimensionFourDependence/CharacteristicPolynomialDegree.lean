import DimensionFourDependence.GaussCharacteristicNonplanarity
import DimensionFourDependence.PrimitiveRationalVector

/-! # Primitive polynomial coordinates of a nonplanar characteristic

Four independent polynomial coordinates cannot all have degree at most
two, since that polynomial space has dimension three. Every actual
nonplanar characteristic has a primitive polynomial representative;
its four coordinates are independent, so one has degree at least three.
This is a parameter-coordinate degree bound; the projective image-degree
comparison is a separate geometric assertion.
-/

namespace DimensionFourDependence

open Matrix Module

variable {K : Type*} [Field K]

/-- Four independent one-variable polynomials include one of degree
at least three. -/
theorem four_independent_polynomials_exists_natDegree_ge_three
    (v : Fin 4 → Polynomial K) (hv : LinearIndependent K v) :
    ∃ i, 3 ≤ (v i).natDegree := by
  by_contra hn
  push Not at hn
  have hdeg (i : Fin 4) : v i ∈ Polynomial.degreeLT K 3 := by
    apply Polynomial.mem_degreeLT.mpr
    exact (Polynomial.degree_le_natDegree).trans_lt (WithBot.coe_lt_coe.mpr (hn i))
  let x : Fin 4 → Polynomial.degreeLT K 3 := fun i => ⟨v i, hdeg i⟩
  have hx : LinearIndependent K x := by
    apply LinearIndependent.of_comp (Polynomial.degreeLT K 3).subtype
    exact hv
  have hdim : finrank K (Polynomial.degreeLT K 3) = 3 := by
    rw [(Polynomial.degreeLTEquiv K 3).finrank_eq]
    simp
  have hbound := hx.fintype_card_le_finrank
  rw [Fintype.card_fin, hdim] at hbound
  omega

/-- Absence of a constant projective hyperplane means independence of
the actual rational coordinate functions over the original field. -/
theorem rational_vector_independent_of_no_constant_hyperplane {n : ℕ}
    (b : Fin n → RatFunc K)
    (hplane : ∀ c : Fin n → K, (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ b = 0 → c = 0) :
    LinearIndependent K b := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hz := hplane c (by simpa only [dotProduct, Algebra.smul_def] using hc)
  exact congrFun hz i

/-- A nonzero nonplanar rational vector supplies actual primitive,
independent polynomial coordinates and a nonzero scalar presentation.
At least one polynomial coordinate has degree three or more. -/
theorem nonplanar_rational_vector_primitive_polynomial_degree_bound
    (b : Fin 4 → RatFunc K) (hb : b ≠ 0)
    (hplane : ∀ c : Fin 4 → K, (fun i => algebraMap K (RatFunc K) (c i)) ⬝ᵥ b = 0 → c = 0) :
    ∃ v : Fin 4 → Polynomial K, v ≠ 0 ∧ LinearIndependent K v ∧
      (∀ r : Polynomial K, (∀ i, r ∣ v i) → IsUnit r) ∧
      (∃ s : RatFunc K, s ≠ 0 ∧ ∀ i, b i = s * algebraMap (Polynomial K) (RatFunc K) (v i)) ∧
      ∃ i, 3 ≤ (v i).natDegree := by
  obtain ⟨v, hv0, hprim, s, hs, hrep⟩ := rational_vector_primitive_polynomial_presentation b hb
  let f : Polynomial K →ₗ[K] RatFunc K :=
    s • (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K)).toLinearMap
  have hLI : LinearIndependent K v := by
    apply LinearIndependent.of_comp f
    convert rational_vector_independent_of_no_constant_hyperplane b hplane using 1
    funext i
    exact (hrep i).symm
  exact ⟨v, hv0, hLI, hprim, ⟨s, hs, hrep⟩,
    four_independent_polynomials_exists_natDegree_ge_three v hLI⟩

universe u

variable {K' : Type u} [Field K'] [CharZero K']

/-- In the actual characteristic-tangent case, primitive polynomial
coordinates, their independence, and the parameter degree lower bound
are all derived from the original homogeneous map. -/
theorem actual_characteristic_tangent_primitive_polynomial_degree_bound
    (H : Fin 4 → MvPolynomial (Fin 4) K') {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (e : RatFunc K' ≃ₐ[K'] projectiveRatioField (K := K')
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (b : Fin 4 → RatFunc K') (hb : b ≠ 0)
    (hspan : normalRulingSubspace (rationalParameterDerivative K') (gaussParameterNormal H I e) =
      Submodule.span (RatFunc K') (Set.range ![b, fun i => rationalParameterDerivative K' (b i)])) :
    ∃ v : Fin 4 → Polynomial K', v ≠ 0 ∧ LinearIndependent K' v ∧
      (∀ r : Polynomial K', (∀ i, r ∣ v i) → IsUnit r) ∧
      (∃ s : RatFunc K', s ≠ 0 ∧ ∀ i, b i = s * algebraMap (Polynomial K') (RatFunc K') (v i)) ∧
      ∃ i, 3 ≤ (v i).natDegree :=
  nonplanar_rational_vector_primitive_polynomial_degree_bound b hb
    (actual_characteristic_tangent_has_no_constant_hyperplane H hd hH hind I e b hspan)

end DimensionFourDependence
