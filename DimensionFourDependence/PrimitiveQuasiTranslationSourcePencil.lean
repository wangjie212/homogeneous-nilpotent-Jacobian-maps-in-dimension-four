import DimensionFourDependence.HomogeneousRankTwoProjectiveParameter
import DimensionFourDependence.SourcePencilProjectiveFibers
import DimensionFourDependence.QuasiTranslationInvariantDivisors
import DimensionFourDependence.PrimitiveParameterLinearForm
import DimensionFourDependence.PrimitiveBinaryDirection

/-! # The primitive quasi-translation constructs actual invariant image-line hypersurfaces -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3000000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- A primitive positive homogeneous vector cannot lie in one fixed
nonzero constant direction. Some original constant cross combination
is nonzero for every specified nonzero direction. -/
theorem primitive_positive_homogeneous_vector_has_nonzero_constant_cross_combination
    (u : Fin 4 → R₀) {e : ℕ} (he : 0 < e) (hhom : IsHomogMap u e)
    (hprim : IsPrimitiveVec u) (c : Fin 4 → K) (hc : c ≠ 0) :
    ∃ i j, C (c j) * u i - C (c i) * u j ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hc
  have hinv : C ((c j)⁻¹) * C (c j) = (1 : R₀) := by
    rw [← map_mul, inv_mul_cancel₀ hj, map_one]
  apply positive_homogeneous_polynomial_not_isUnit (u j) he (hhom j)
  apply hprim (u j)
  intro i
  have hrep : u i = C ((c j)⁻¹) * C (c i) * u j := by
    calc
      u i = C ((c j)⁻¹) * (C (c j) * u i) := by rw [← mul_assoc, hinv, one_mul]
      _ = _ := by rw [sub_eq_zero.mp (hn i j)]; ring
  exact ⟨C ((c j)⁻¹) * C (c i), by rw [hrep]; ring⟩

/-- Every literal member of a reduced projective source pencil is an
actual polynomial invariant of the primitive quasi-translation. Each
member divides a constructed nonzero constant combination of the original
direction entries, so factorial closure applies without a generic choice. -/
theorem primitive_quasi_translation_reduced_source_pencil_member_is_invariant
    (u : Fin 4 → R₀) {e : ℕ} (he : 0 < e) (hhom : IsHomogMap u e)
    (hprim : IsPrimitiveVec u) (hacc : jac u *ᵥ u = 0)
    (p q : R₀) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (v : Fin 4 → Polynomial K)
    (hv : ∀ f : Polynomial K, (∀ i, f ∣ v i) → IsUnit f) (r : F₀)
    (hrep : ∀ i, algebraMap R₀ F₀ (u i) =
      r * Polynomial.aeval (algebraMap R₀ F₀ p / algebraMap R₀ F₀ q) (v i)) (a : K) :
    polynomialVectorDerivation u (p - C a * q) = 0 := by
  let c : Fin 4 → K := fun i => (v i).eval a
  have hc : c ≠ 0 := by
    obtain ⟨i, hi⟩ := primitive_parameter_covector_no_constant_base_point v hv a
    exact fun hz => hi (congrFun hz i)
  obtain ⟨i, j, hnonzero⟩ :=
    primitive_positive_homogeneous_vector_has_nonzero_constant_cross_combination u he hhom hprim c hc
  have hi := polynomialVectorDerivation_output_zero_of_kernel u u hacc i
  have hj := polynomialVectorDerivation_output_zero_of_kernel u u hacc j
  have hinvariant : polynomialVectorDerivation u (C (c j) * u i - C (c i) * u j) = 0 := by
    rw [← smul_eq_C_mul, ← smul_eq_C_mul, map_sub, Derivation.map_smul, Derivation.map_smul, hi, hj]
    simp
  exact zero_acceleration_polynomial_invariant_divisor_is_invariant u hacc _ hnonzero hinvariant _
    (reduced_source_pencil_divides_original_projective_cross_equations u p q hq hrel v r hrep a i j)

/-- The two original members of the source pencil are invariant as
well, by its literal parameter values zero and one. -/
theorem primitive_quasi_translation_reduced_source_pencil_generators_are_invariant
    (u : Fin 4 → R₀) {e : ℕ} (he : 0 < e) (hhom : IsHomogMap u e)
    (hprim : IsPrimitiveVec u) (hacc : jac u *ᵥ u = 0)
    (p q : R₀) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (v : Fin 4 → Polynomial K)
    (hv : ∀ f : Polynomial K, (∀ i, f ∣ v i) → IsUnit f) (r : F₀)
    (hrep : ∀ i, algebraMap R₀ F₀ (u i) =
      r * Polynomial.aeval (algebraMap R₀ F₀ p / algebraMap R₀ F₀ q) (v i)) :
    polynomialVectorDerivation u p = 0 ∧ polynomialVectorDerivation u q = 0 := by
  have h0 := primitive_quasi_translation_reduced_source_pencil_member_is_invariant
    u he hhom hprim hacc p q hq hrel v hv r hrep 0
  have h1 := primitive_quasi_translation_reduced_source_pencil_member_is_invariant
    u he hhom hprim hacc p q hq hrel v hv r hrep 1
  have hp : polynomialVectorDerivation u p = 0 := by simpa only [map_zero, zero_mul, sub_zero] using h0
  refine ⟨hp, ?_⟩
  simpa only [map_one, one_mul, map_sub, hp, zero_sub, neg_eq_zero] using h1

/-- The original primitive positive homogeneous quasi-translation
constructs a reduced homogeneous invariant pencil and a primitive
polynomial parameter direction. Every literal pencil hypersurface is
nonzero, has the same actual degree, and its entire original affine
zero locus maps into the specified nonzero parameter line. -/
theorem primitive_positive_quasi_translation_constructs_invariant_image_line_source_pencil
    (u : Fin 4 → R₀) {e : ℕ} (he : 0 < e) (hUne : u ≠ 0)
    (hhom : IsHomogMap u e) (hprim : IsPrimitiveVec u) (hacc : jac u *ᵥ u = 0) :
    ∃ (p q : R₀) (D : ℕ) (v : Fin 4 → Polynomial K) (t r : F₀),
      0 < D ∧ p ≠ 0 ∧ q ≠ 0 ∧ p.IsHomogeneous D ∧ q.IsHomogeneous D ∧ IsRelPrime p q ∧
      Transcendental K t ∧ t = algebraMap R₀ F₀ p / algebraMap R₀ F₀ q ∧ v ≠ 0 ∧
      (∀ f : Polynomial K, (∀ i, f ∣ v i) → IsUnit f) ∧ r ≠ 0 ∧
      (∀ i, algebraMap R₀ F₀ (u i) = r * Polynomial.aeval t (v i)) ∧
      polynomialVectorDerivation u p = 0 ∧ polynomialVectorDerivation u q = 0 ∧
      ∀ a : K, p - C a * q ≠ 0 ∧ (p - C a * q).IsHomogeneous D ∧
        (p - C a * q).totalDegree = D ∧ (fun i => (v i).eval a) ≠ 0 ∧
        ∀ z : Fin 4 → K, aeval z (p - C a * q) = 0 → ∀ i j,
          aeval z (u i) * (v j).eval a = aeval z (u j) * (v i).eval a := by
  have hrank := primitive_positive_homogeneous_quasi_translation_rank_two u he hUne hhom hprim hacc
  obtain ⟨a, ha⟩ : ∃ a, u a ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hUne
  obtain ⟨φ, _hφ, ht, _hEuler, p, q, D, hD, hp, hq, hpH, hqH, hrel, htfrac,
    v, r, hv, hprimitive, hr, hrep⟩ :=
    homogeneous_rank_two_map_constructs_primitive_projective_parameter_and_source_pencil u he hhom hrank a ha
  have hrep' : ∀ i, algebraMap R₀ F₀ (u i) =
      r * Polynomial.aeval (algebraMap R₀ F₀ p / algebraMap R₀ F₀ q) (v i) := by
    simpa only [htfrac] using hrep
  obtain ⟨hDp, hDq⟩ := primitive_quasi_translation_reduced_source_pencil_generators_are_invariant
    u he hhom hprim hacc p q hq hrel v hprimitive r hrep'
  refine ⟨p, q, D, v, φ RatFunc.X, r, hD, hp, hq, hpH, hqH, hrel, ht, htfrac,
    hv, hprimitive, hr, hrep, hDp, hDq, ?_⟩
  intro b
  have hqF : algebraMap R₀ F₀ q ≠ 0 :=
    fun hz => hq (IsFractionRing.injective R₀ F₀ (hz.trans (map_zero _).symm))
  have hmember : p - C b * q ≠ 0 := by
    intro hz
    have hconst : φ RatFunc.X = algebraMap K F₀ b := by
      rw [htfrac, sub_eq_zero.mp hz, map_mul, mul_div_cancel_right₀ _ hqF]
      exact (IsScalarTower.algebraMap_apply K R₀ F₀ b).symm
    exact ht (hconst ▸ isAlgebraic_algebraMap b)
  have hmemberhom : (p - C b * q).IsHomogeneous D := hpH.sub (hqH.C_mul b)
  have hnonzero : (fun i => (v i).eval b) ≠ 0 := by
    obtain ⟨i, hi⟩ := primitive_parameter_covector_no_constant_base_point v hprimitive b
    exact fun hz => hi (congrFun hz i)
  exact ⟨hmember, hmemberhom, hmemberhom.totalDegree hmember, hnonzero,
    fun z hz i j => reduced_source_pencil_zero_locus_maps_into_parameter_line u p q hq hrel v r hrep' b z hz i j⟩

end DimensionFourDependence
