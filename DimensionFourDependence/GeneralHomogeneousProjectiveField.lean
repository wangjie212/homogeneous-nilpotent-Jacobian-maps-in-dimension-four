import DimensionFourDependence.HomogeneousRankTwoProjectiveParameter

/-! # Actual homogeneous projective fields in arbitrary finite source dimension -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 4000000

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}
local notation "R₀" => MvPolynomial (Fin n) K
local notation "F₀" => FractionRing (MvPolynomial (Fin n) K)

theorem general_projective_ratio_field_common_weight_constants
    (D : Derivation K F F) (Y : Fin n → F) (a : Fin n) (w : F)
    (hY : ∀ i, D (Y i) = w * Y i) :
    projectiveRatioField (K := K) Y a ≤ derivationConstants D := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  change D (Y i / Y a) = 0
  rw [D.leibniz_div, hY i, hY a]
  simp only [smul_eq_mul]
  ring


theorem general_projective_ratio_field_adjoin_output_eq_full
    (Y : Fin n → F) (a : Fin n) (ha : Y a ≠ 0) :
    (IntermediateField.adjoin (projectiveRatioField (K := K) Y a) {Y a}).restrictScalars K =
      fullOutputField (K := K) Y := by
  rw [projectiveRatioField, IntermediateField.adjoin_adjoin_left]
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rcases hx with ⟨i, rfl⟩ | rfl
    · exact (fullOutputField (K := K) Y).div_mem
        (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
        (IntermediateField.subset_adjoin K _ ⟨a, rfl⟩)
    · exact IntermediateField.subset_adjoin K _ ⟨a, rfl⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    rw [← div_mul_cancel₀ (Y i) ha]
    exact (IntermediateField.adjoin K (Set.range (fun i => Y i / Y a) ∪ {Y a})).mul_mem
      (IntermediateField.subset_adjoin K _ (Or.inl ⟨i, rfl⟩))
      (IntermediateField.subset_adjoin K _ (Or.inr rfl))

theorem general_full_output_field_trdeg_eq_projective_ratio_field_add_one
    (Y : Fin n → F) (a : Fin n) (ha : Y a ≠ 0)
    (ht : Transcendental (projectiveRatioField (K := K) Y a) (Y a)) :
    Algebra.trdeg K (fullOutputField (K := K) Y) =
      Algebra.trdeg K (projectiveRatioField (K := K) Y a) + 1 := by
  let R := projectiveRatioField (K := K) Y a
  let J := IntermediateField.adjoin R {Y a}
  have hd : Algebra.trdeg R J = 1 :=
    generatedField_singleton_trdeg_one_of_transcendental (K := R) (Y a) ht
  let : FaithfulSMul K R :=
    (faithfulSMul_iff_algebraMap_injective K R).mpr (algebraMap K R).injective
  let : FaithfulSMul R J :=
    (faithfulSMul_iff_algebraMap_injective R J).mpr (algebraMap R J).injective
  have he := trdeg_add_eq (A := J) K R
  rw [hd] at he
  calc
    _ = Algebra.trdeg K (J.restrictScalars K) := by
      rw [general_projective_ratio_field_adjoin_output_eq_full Y a ha]
    _ = Algebra.trdeg K J := rfl
    _ = _ := he.symm

theorem general_homogeneous_output_transcendental_over_projective_ratios
    (H : Fin n → MvPolynomial (Fin n) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (a : Fin n) (ha : H a ≠ 0) :
    Transcendental (projectiveRatioField (K := K)
      (fun i => algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (H i)) a)
      (algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (H a)) := by
  let Y : Fin n → FractionRing (MvPolynomial (Fin n) K) :=
    fun i => algebraMap (MvPolynomial (Fin n) K) _ (H i)
  have hw : (d : FractionRing (MvPolynomial (Fin n) K)) ≠ 0 := by exact_mod_cast hd.ne'
  have hY : ∀ i, sourceEuler (K := K) (Y i) = (d : FractionRing (MvPolynomial (Fin n) K)) * Y i :=
    fun i => sourceEuler_homogeneous (H i) (hH i)
  have hYa : Y a ≠ 0 := by
    intro hz
    apply ha
    apply IsFractionRing.injective (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
    simpa only [map_zero] using hz
  exact nonzero_weight_transcendental_over_constant_subfield (sourceEuler (K := K))
    (projectiveRatioField (K := K) Y a)
    (general_projective_ratio_field_common_weight_constants _ Y a _ hY) (Y a) _ hYa hw (hY a)

theorem general_polynomial_output_field_trdeg_eq_rank
    (H : Fin n → MvPolynomial (Fin n) K) :
    Algebra.trdeg K (polynomialOutputField H) = polyRank (jac H) := by
  have he := rationalJacobian_rank_eq_output_trdeg
    (fun i => algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (H i))
  rw [rationalJacobian_polynomial H] at he
  exact he

theorem general_homogeneous_output_trdeg_eq_projective_add_one
    (H : Fin n → MvPolynomial (Fin n) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (a : Fin n) (ha : H a ≠ 0) :
    Algebra.trdeg K (polynomialOutputField H) =
      Algebra.trdeg K (projectiveRatioField (K := K)
        (fun i => algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (H i)) a) + 1 := by
  have hYa : algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)) (H a) ≠ 0 := by
    intro hz
    apply ha
    apply IsFractionRing.injective (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
    simpa only [map_zero] using hz
  exact general_full_output_field_trdeg_eq_projective_ratio_field_add_one _ a hYa
    (general_homogeneous_output_transcendental_over_projective_ratios H hd hH a ha)

theorem general_homogeneous_rank_two_projective_ratio_field_trdeg_one
    (H : Fin n → R₀) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 2) (a : Fin n) (ha : H a ≠ 0) :
    Algebra.trdeg K (projectiveRatioField (K := K)
      (fun i => algebraMap R₀ F₀ (H i)) a) = 1 := by
  let M := projectiveRatioField (K := K) (fun i => algebraMap R₀ F₀ (H i)) a
  have he := general_homogeneous_output_trdeg_eq_projective_add_one H hd hH a ha
  rw [(general_polynomial_output_field_trdeg_eq_rank H).trans
    (congrArg (fun n : ℕ => (n : Cardinal)) hrank)] at he
  change 2 = Algebra.trdeg K M + 1 at he
  have hle : Algebra.trdeg K M ≤ 2 := (self_le_add_right _ 1).trans_eq he.symm
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (hle.trans_lt (by simp))
  rw [hn] at he
  have hn' : 2 = n + 1 := by exact_mod_cast he
  have hn1 : n = 1 := by omega
  change Algebra.trdeg K M = 1
  rw [hn, hn1]
  rfl

end DimensionFourDependence
