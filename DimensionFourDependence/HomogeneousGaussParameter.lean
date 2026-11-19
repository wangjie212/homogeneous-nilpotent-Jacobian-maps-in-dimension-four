import DimensionFourDependence.GaussRulingIncidence
import DimensionFourDependence.Homogeneous

/-! # The actual Gauss parameter is a reduced homogeneous source quotient

Equal-degree homogeneous polynomial quotients are closed under all field
operations. Thus every element of the actual projective ratio field has
such a presentation. Removing a homogeneous common factor gives relatively
prime numerator and denominator of the same degree. For a transcendental
parameter that common degree is positive.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

local notation "R" => MvPolynomial (Fin 4) K
local notation "F" => FractionRing (MvPolynomial (Fin 4) K)

/-- The realized rational Gauss parameter has exactly the actual
Gauss field as the range of its rational-function realization. -/
theorem gaussParameterSourceHom_fieldRange
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    (gaussParameterSourceHom H I e).fieldRange =
      projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I) := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact (e r).property
  · intro hx
    obtain ⟨r, hr⟩ := e.surjective ⟨x, hx⟩
    exact ⟨r, congrArg Subtype.val hr⟩

/-- The actual source-field Gauss parameter generates precisely the
actual projective-normal ratio field. -/
theorem actual_gauss_field_eq_adjoin_realized_parameter
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    IntermediateField.adjoin K {gaussParameterSourceHom H I e RatFunc.X} =
      projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I) := by
  have he := congrArg (IntermediateField.map (gaussParameterSourceHom H I e)) (RatFunc.adjoin_X (K := K))
  rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
    gaussParameterSourceHom_fieldRange] at he
  exact he

/-- Every element of the field of equally homogeneous projective
ratios has an actual equal-degree homogeneous polynomial quotient. -/
theorem projective_ratio_field_homogeneous_fraction
    (N : Fin 4 → R) {d : ℕ} (hN : IsHomogMap N d) (a : Fin 4) (ha : N a ≠ 0)
    (t : F) (ht : t ∈ projectiveRatioField (K := K)
      (fun i => algebraMap R F (N i)) a) :
    ∃ p q : R, ∃ e : ℕ, q ≠ 0 ∧ p.IsHomogeneous e ∧ q.IsHomogeneous e ∧
      t = algebraMap R F p / algebraMap R F q := by
  have hmap {p : R} (hp : p ≠ 0) : algebraMap R F p ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hp
  induction ht using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨N i, N a, d, ha, hN i, hN a, rfl⟩
  | algebraMap k =>
    refine ⟨C k, 1, 0, one_ne_zero, isHomogeneous_C _ _, isHomogeneous_one _ _, ?_⟩
    simp only [map_one, div_one]
    rfl
  | add x y hx hy ihx ihy =>
    obtain ⟨p, q, e, hq, hpH, hqH, hxp⟩ := ihx
    obtain ⟨r, s, f, hs, hrH, hsH, hyr⟩ := ihy
    refine ⟨p * s + r * q, q * s, e + f, mul_ne_zero hq hs,
      (hpH.mul hsH).add (by simpa only [add_comm] using hrH.mul hqH), hqH.mul hsH, ?_⟩
    rw [hxp, hyr, map_add, map_mul, map_mul, map_mul]
    field_simp [hmap hq, hmap hs]
  | inv x hx ih =>
    obtain ⟨p, q, e, hq, hpH, hqH, hxp⟩ := ih
    by_cases hp : p = 0
    · refine ⟨0, 1, 0, one_ne_zero, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, ?_⟩
      rw [hxp, hp, map_zero, zero_div, inv_zero, map_one, div_one]
    · refine ⟨q, p, e, hp, hqH, hpH, ?_⟩
      rw [hxp, inv_div]
  | mul x y hx hy ihx ihy =>
    obtain ⟨p, q, e, hq, hpH, hqH, hxp⟩ := ihx
    obtain ⟨r, s, f, hs, hrH, hsH, hyr⟩ := ihy
    refine ⟨p * r, q * s, e + f, mul_ne_zero hq hs, hpH.mul hrH, hqH.mul hsH, ?_⟩
    rw [hxp, hyr, map_mul, map_mul, div_mul_div_comm]

/-- Equal homogeneous quotient degrees survive removal of their
common factor, yielding an actual relatively prime homogeneous pair. -/
theorem homogeneous_fraction_reduced_pair
    (t : F) (p q : R) {e : ℕ} (hq : q ≠ 0)
    (hpH : p.IsHomogeneous e) (hqH : q.IsHomogeneous e)
    (ht : t = algebraMap R F p / algebraMap R F q) :
    ∃ P Q : R, ∃ D : ℕ, Q ≠ 0 ∧ P.IsHomogeneous D ∧ Q.IsHomogeneous D ∧
      IsRelPrime P Q ∧ t = algebraMap R F P / algebraMap R F Q := by
  let W : Fin 2 → R := ![p, q]
  have hW : IsHomogMap W e := by
    intro i
    fin_cases i <;> assumption
  have hW0 : W ≠ 0 := by
    intro hz
    exact hq (congrFun hz 1)
  obtain ⟨g, V, c, _, hg, _, hV, hprim, hWV⟩ := exists_primitive_factorization e W hW hW0
  have hp : p = g * V 0 := congrFun hWV 0
  have hq' : q = g * V 1 := congrFun hWV 1
  have hQ : V 1 ≠ 0 := by
    intro hz
    exact hq (by rw [hq', hz, mul_zero])
  have hgF : algebraMap R F g ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hg
  refine ⟨V 0, V 1, e - c, hQ, hV 0, hV 1, ?_, ?_⟩
  · intro r hr0 hr1
    apply hprim r
    intro i
    fin_cases i <;> assumption
  · rw [ht, hp, hq', map_mul, map_mul, mul_div_mul_left _ _ hgF]

/-- The actual realized Gauss parameter has relatively prime
homogeneous numerator and denominator of the same positive degree. -/
theorem actual_gauss_parameter_reduced_homogeneous_source_quotient
    (H : Fin 4 → R) {d : ℕ} (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    ∃ p q : R, ∃ D : ℕ, 0 < D ∧ p ≠ 0 ∧ q ≠ 0 ∧
      p.IsHomogeneous D ∧ q.IsHomogeneous D ∧ IsRelPrime p q ∧
      gaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q := by
  let t := gaussParameterSourceHom H I e RatFunc.X
  have ht : Transcendental K t := gaussParameterSourceHom_X_transcendental H I e
  have hmem : t ∈ projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I) :=
    (e RatFunc.X).property
  have hpivot : imageRelationNormal H I.equation (imageNormalPivot H I) ≠ 0 := by
    intro hz
    apply imageNormalPivot_ne_zero H I
    simp only [rationalImageNormal, hz, map_zero]
  obtain ⟨p, q, D, hq, hpH, hqH, hrep⟩ := projective_ratio_field_homogeneous_fraction
    (imageRelationNormal H I.equation) (I.normal_homogeneous H hH) (imageNormalPivot H I) hpivot t hmem
  obtain ⟨P, Q, E, hQ, hPH, hQH, hrel, he⟩ := homogeneous_fraction_reduced_pair t p q hq hpH hqH hrep
  have hP : P ≠ 0 := by
    intro hz
    rw [he, hz, map_zero, zero_div] at ht
    exact ht isAlgebraic_zero
  have hE : 0 < E := by
    by_contra hn
    have hzero : E = 0 := by omega
    have hpC := eq_C_of_isHomogeneous_zero (hzero ▸ hPH)
    have hqC := eq_C_of_isHomogeneous_zero (hzero ▸ hQH)
    have hs : t = algebraMap K F (P.coeff 0 / Q.coeff 0) := by
      rw [he, hpC, hqC, map_div₀]
      simp only [coeff_C]
      rfl
    rw [hs] at ht
    exact ht (isAlgebraic_algebraMap _)
  exact ⟨P, Q, E, hE, hP, hQ, hPH, hQH, hrel, he⟩

end DimensionFourDependence
