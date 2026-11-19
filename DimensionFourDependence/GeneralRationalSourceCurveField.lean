import DimensionFourDependence.RationalSourceCurveField

/-! # Actual curve subfields of a rational source in arbitrary finite dimension -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 4000000

variable {K : Type u} [Field K] [CharZero K] {n r : ℕ}
local notation "R" => MvPolynomial (Fin r) K
local notation "F" => FractionRing (MvPolynomial (Fin r) K)

theorem general_source_curve_field_embeds_in_ratFunc
    (x : Fin n → F) (hdim : Algebra.trdeg K (fullOutputField (K := K) x) = 1) :
    Nonempty (fullOutputField (K := K) x →ₐ[K] RatFunc K) := by
  classical
  have hnonconstant : ∃ i, ¬ ∃ c : K, x i = algebraMap K F c := by
    by_contra hn
    push Not at hn
    choose c hc using hn
    have hbot : fullOutputField (K := K) x = ⊥ := by
      apply bot_unique
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨i, rfl⟩
      rw [hc i]
      exact (⊥ : IntermediateField K F).algebraMap_mem (c i)
    have hz : Algebra.trdeg K (fullOutputField (K := K) x) = 0 := by
      rw [hbot]
      exact trdeg_eq_zero
    exact one_ne_zero (hdim.symm.trans hz)
  obtain ⟨i, hi⟩ := hnonconstant
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) x
  choose N hN using hD
  have hD0 : (D : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp D.property
  have hDF : algebraMap R F (D : R) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hD0
  have hrep (j : Fin n) : x j = algebraMap R F (N j) / algebraMap R F (D : R) := by
    apply (eq_div_iff hDF).mpr
    have he := hN j
    simp only [Algebra.smul_def] at he
    rw [mul_comm, ← he]
  have hnot : ¬ ∃ c : K, N i = c • (D : R) := by
    rintro ⟨c, hc⟩
    apply hi
    refine ⟨c, ?_⟩
    rw [hrep i, hc, MvPolynomial.smul_eq_C_mul, map_mul]
    exact mul_div_cancel_right₀ _ hDF
  obtain ⟨p, q, _, _, hline, ht⟩ := exists_source_line_transcendental_ratio (N i) (D : R) hD0 hnot
  let g := sourceLineRationalSpecialization p q
  have hgD : g (D : R) ≠ 0 := by
    intro hz
    apply hline
    apply IsFractionRing.injective (Polynomial K) (RatFunc K)
    simpa only [g, sourceLineRationalSpecialization_apply, map_zero] using hz
  let y : Fin n → RatFunc K := fun j => g (N j) / g (D : R)
  let f := IsScalarTower.toAlgHom K R F
  have hf : Function.Injective f := IsFractionRing.injective R F
  have hrel : ∀ P : MvPolynomial (Fin n) K, aeval x P = 0 → aeval y P = 0 := by
    intro P hP
    apply ratio_polynomial_relations_specialize f hf g (D : R) hDF hgD N P
    change aeval (fun j => algebraMap R F (N j) / algebraMap R F (D : R)) P = 0
    simpa only [← hrep] using hP
  have hy : Transcendental K (y i) := ht
  obtain ⟨φ, _⟩ := exists_curve_function_field_embedding_of_specialization x y hdim hrel i hy
  exact ⟨φ⟩

theorem general_source_curve_field_rational
    (x : Fin n → F) (hdim : Algebra.trdeg K (fullOutputField (K := K) x) = 1) :
    Nonempty (RatFunc K ≃ₐ[K] fullOutputField (K := K) x) := by
  obtain ⟨f⟩ := general_source_curve_field_embeds_in_ratFunc x hdim
  exact rational_function_equiv_of_curve_field_embedding f hdim

end DimensionFourDependence
