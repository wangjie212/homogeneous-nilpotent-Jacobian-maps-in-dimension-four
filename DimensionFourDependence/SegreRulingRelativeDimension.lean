import DimensionFourDependence.SegreRulingParameterField

/-! # The original output field has dimension two over each actual ruling field -/

namespace DimensionFourDependence

attribute [local instance] coefficientFieldScalarTower

set_option maxHeartbeats 3000000

universe u
variable {K : Type u} [Field K] [CharZero K]
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual source ruling field embeds in the original coefficient
field through its original-source inclusion. -/
theorem segre_source_ruling_field_le_coefficient_field
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    (segreSourceRulingParameterHom Y hY j hj).fieldRange ≤ (coefficientField (K := K) Y).restrictScalars K := by
  apply (segre_source_ruling_parameter_fieldRange_le_output Y hY j hj).trans
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  exact (coefficientCoordinate (K := K) Y i).property

/-- The actual ruling-field inclusion into the original coefficient field. -/
noncomputable def segreRulingFieldCoefficientHom
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    (segreSourceRulingParameterHom Y hY j hj).fieldRange →ₐ[K] coefficientField (K := K) Y :=
  IntermediateField.inclusion (segre_source_ruling_field_le_coefficient_field Y hY j hj)

theorem segreRulingFieldCoefficientHom_source
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0)
    (a : (segreSourceRulingParameterHom Y hY j hj).fieldRange) :
    algebraMap (coefficientField (K := K) Y) S₀ (segreRulingFieldCoefficientHom Y hY j hj a) = (a : S₀) := rfl

/-- The original ruling parameter as an actual element of its source subfield. -/
noncomputable def segreRulingFieldParameter
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    (segreSourceRulingParameterHom Y hY j hj).fieldRange :=
  (segreSourceRulingParameterHom Y hY j hj).equivFieldRange RatFunc.X

theorem segreRulingFieldParameter_source
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    (segreRulingFieldParameter Y hY j hj : S₀) = Y j / Y 0 :=
  segreSourceRulingParameterHom_X Y hY j hj

theorem segreRulingFieldCoefficientHom_parameter
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    segreRulingFieldCoefficientHom Y hY j hj (segreRulingFieldParameter Y hY j hj) =
      segreCoefficientRulingParameter Y j := by
  apply (algebraMap (coefficientField (K := K) Y) S₀).injective
  rw [segreRulingFieldCoefficientHom_source, segreRulingFieldParameter_source]
  rfl

/-- Adjoining the original independent output triple over its actual
ruling field leaves precisely two independent output parameters. -/
theorem segre_ruling_relative_output_triple_trdeg_two
    (Y : Fin 3 → S₀) (hY : AlgebraicIndependent K Y) (j : Fin 3) (hj : j ≠ 0) :
    Algebra.trdeg (segreSourceRulingParameterHom Y hY j hj).fieldRange
      (IntermediateField.adjoin (segreSourceRulingParameterHom Y hY j hj).fieldRange (Set.range Y)) = 2 := by
  let M := (segreSourceRulingParameterHom Y hY j hj).fieldRange
  let J := IntermediateField.adjoin M (Set.range Y)
  let : FaithfulSMul K M := (faithfulSMul_iff_algebraMap_injective K M).mpr (algebraMap K M).injective
  let : FaithfulSMul M J := (faithfulSMul_iff_algebraMap_injective M J).mpr (algebraMap M J).injective
  have hM : Algebra.trdeg K M = 1 := rational_parameter_fieldRange_trdeg_one _
  have hJ : Algebra.trdeg K J = 3 := by
    change Algebra.trdeg K (J.restrictScalars K) = 3
    have he : J.restrictScalars K = fullOutputField (K := K) Y := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]
      exact sup_eq_right.mpr (segre_source_ruling_parameter_fieldRange_le_output Y hY j hj)
    rw [he]
    exact (rationalOutputEquiv Y hY).trdeg_eq.symm.trans (rationalSource_trdeg_eq (K := K) (n := 3))
  have he := trdeg_add_eq (A := J) K M
  rw [hM, hJ] at he
  have hle : Algebra.trdeg M J ≤ 3 := le_add_self.trans_eq he
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (hle.trans_lt (by simp))
  rw [hn] at he
  have hn' : 1 + n = 3 := by exact_mod_cast he
  have hn2 : n = 2 := by omega
  change Algebra.trdeg M J = 2
  rw [hn, hn2]
  norm_num

/-- For the actual Segre output vector the same relative dimension
holds for all four coordinates, using the original determinant identity. -/
theorem segre_ruling_relative_full_output_trdeg_two
    (Q : Fin 4 → S₀) (hY : AlgebraicIndependent K (fun i : Fin 3 => Q i.castSucc))
    (hQ0 : Q 0 ≠ 0) (hquad : Q 0 * Q 3 - Q 1 * Q 2 = 0) (j : Fin 3) (hj : j ≠ 0) :
    Algebra.trdeg (segreSourceRulingParameterHom (fun i : Fin 3 => Q i.castSucc) hY j hj).fieldRange
      (IntermediateField.adjoin (segreSourceRulingParameterHom (fun i : Fin 3 => Q i.castSucc) hY j hj).fieldRange
        (Set.range Q)) = 2 := by
  let M := (segreSourceRulingParameterHom (fun i : Fin 3 => Q i.castSucc) hY j hj).fieldRange
  have he := segre_first_three_generate_output_field (K := M) Q hQ0 hquad
  change Algebra.trdeg M (fullOutputField (K := M) Q) = 2
  rw [← he]
  exact segre_ruling_relative_output_triple_trdeg_two _ hY j hj

end DimensionFourDependence
