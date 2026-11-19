import DimensionFourDependence.PrimitiveQuasiTranslationClassification
import DimensionFourDependence.QuasiTranslationInvariantDivisors

/-! # The full four-variable homogeneous quasi-translation span bound -/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] {n : ℕ}
local notation "P₀" => MvPolynomial (Fin n) K

/-- Scaling the polynomial direction scales its entire directional
derivation, including values on its own component polynomials. -/
theorem polynomialVectorDerivation_scalar_direction
    (g : P₀) (u : Fin n → P₀) (p : P₀) :
    polynomialVectorDerivation (fun i => g * u i) p = g * polynomialVectorDerivation u p := by
  simp only [polynomialVectorDerivation_apply, Finset.mul_sum, mul_assoc]

variable [CharZero K]

/-- Removing any nonzero common polynomial factor from a nonzero
quasi-translation preserves zero acceleration. The common factor is
an invariant of the reduced direction. No primitivity is required. -/
theorem zero_acceleration_common_factor_constructs_invariant_factor_and_reduced_direction
    (g : P₀) (hg : g ≠ 0) (u : Fin n → P₀) (hu : u ≠ 0)
    (hacc : jac (fun i => g * u i) *ᵥ (fun i => g * u i) = 0) :
    polynomialVectorDerivation u g = 0 ∧ jac u *ᵥ u = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hu
  have hgInv := zero_acceleration_polynomial_invariant_divisor_is_invariant
    (fun i => g * u i) hacc (g * u i) (mul_ne_zero hg hi)
    (polynomialVectorDerivation_output_zero_of_kernel _ _ hacc i) g (dvd_mul_right g (u i))
  rw [polynomialVectorDerivation_scalar_direction] at hgInv
  have hDg : polynomialVectorDerivation u g = 0 := (mul_eq_zero.mp hgInv).resolve_left hg
  refine ⟨hDg, ?_⟩
  funext j
  have hDj := polynomialVectorDerivation_output_zero_of_kernel _ _ hacc j
  rw [polynomialVectorDerivation_scalar_direction] at hDj
  have hred : polynomialVectorDerivation u (g * u j) = 0 := (mul_eq_zero.mp hDj).resolve_left hg
  rw [(polynomialVectorDerivation u).leibniz, smul_eq_mul, smul_eq_mul, hDg,
    mul_zero, add_zero] at hred
  have hDu : polynomialVectorDerivation u (u j) = 0 := (mul_eq_zero.mp hred).resolve_left hg
  simpa only [Matrix.mulVec, dotProduct, jac, Matrix.of_apply,
    polynomialVectorDerivation_apply, Pi.zero_apply, mul_comm] using hDu

local notation "R₀" => MvPolynomial (Fin 4) K

variable [IsAlgClosed K]

/-- The full positive homogeneous four-variable quasi-translation
has component span at most two, whether or not the original vector
is primitive. Its primitive part and invariant common factor are
constructed from the actual map. -/
theorem positive_homogeneous_four_variable_quasi_translation_component_span_at_most_two
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hacc : jac H *ᵥ H = 0) :
    finrank K (Submodule.span K (Set.range H)) ≤ 2 := by
  classical
  by_cases hH0 : H = 0
  · have hspan : Submodule.span K (Set.range H) = ⊥ := by
      apply le_antisymm _ bot_le
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      simp [hH0]
    rw [hspan]
    simp
  obtain ⟨g, u, c, _hc, hg, _hgh, huh, hprim, hHu⟩ := exists_primitive_factorization d H hH hH0
  have hu : u ≠ 0 := by
    intro hz
    apply hH0
    rw [hHu, hz]
    funext i
    simp
  have hacc' : jac (fun i => g * u i) *ᵥ (fun i => g * u i) = 0 := hHu ▸ hacc
  have hred := (zero_acceleration_common_factor_constructs_invariant_factor_and_reduced_direction
    g hg u hu hacc').2
  by_cases he : d - c = 0
  · have hconst (i) : u i = C ((u i).coeff 0) := eq_C_of_isHomogeneous_zero (he ▸ huh i)
    have hle : Submodule.span K (Set.range H) ≤ Submodule.span K {g} := by
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      rw [hHu]
      change g * u i ∈ Submodule.span K {g}
      rw [hconst]
      have hmem := (Submodule.span K {g}).smul_mem ((u i).coeff 0)
        (Submodule.subset_span (Set.mem_singleton g))
      simpa only [smul_eq_C_mul, mul_comm] using hmem
    have hdim := Submodule.finrank_mono hle
    rw [finrank_span_singleton hg] at hdim
    omega
  · obtain ⟨r, s, hli, hr, hs⟩ :=
      primitive_positive_homogeneous_quasi_translation_constructs_two_constant_relations
        u (Nat.pos_of_ne_zero he) hu huh hprim hred
    have hlift (b : Fin 4 → K) (hb : (∑ i, b i • u i) = 0) :
        (∑ i, b i • H i) = 0 := by
      rw [hHu]
      calc
        _ = g * ∑ i, b i • u i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp only [smul_eq_C_mul]
          ring
        _ = 0 := by rw [hb, mul_zero]
    exact two_independent_constant_relations_bound_component_span H r s hli (hlift r hr) (hlift s hs)

/-- The complete homogeneous quasi-translation branch of the
four-dimensional dependence assertion. No rank, primitive direction,
normal form or span bound is assumed. -/
theorem positive_homogeneous_four_variable_quasi_translation_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hacc : jac H *ᵥ H = 0) : ComponentsDependent H := by
  obtain ⟨r, s, hli, hr, _hs⟩ := component_span_at_most_two_constructs_independent_constant_relations H
    (positive_homogeneous_four_variable_quasi_translation_component_span_at_most_two H hd hH hacc)
  exact ⟨r, by simpa using hli.ne_zero 0, hr⟩

/-- If the original homogeneous Euler vector is killed by the square
Jacobian, Euler's identity gives the actual quasi-translation identity
and hence the complete component-dependence conclusion. -/
theorem homogeneous_four_variable_squared_jacobian_euler_zero_componentsDependent
    (H : Fin 4 → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hzero : jac H ^ 2 *ᵥ coordVec = 0) : ComponentsDependent H := by
  have he := hzero
  rw [pow_two, ← Matrix.mulVec_mulVec, euler_identity H hH, Matrix.mulVec_smul] at he
  have hacc : jac H *ᵥ H = 0 := (smul_eq_zero.mp he).resolve_left (by exact_mod_cast hd.ne')
  exact positive_homogeneous_four_variable_quasi_translation_componentsDependent H hd hH hacc

end DimensionFourDependence
