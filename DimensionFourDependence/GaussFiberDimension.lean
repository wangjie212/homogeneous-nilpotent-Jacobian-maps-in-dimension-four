import DimensionFourDependence.GaussRulingIncidence
import DimensionFourDependence.OutputCoordinateFieldEquiv

/-! # Relative dimension over the actual Gauss field

The actual normal ratios belong to the original output field. Adjoining
the outputs over the Gauss field therefore recovers that same field.
In rank three and Gauss dimension one, the transcendence-degree tower
leaves exactly two output parameters over the actual Gauss field.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

variable {K : Type u} [Field K]

/-- The actual Gauss field is a subfield of the actual output field. -/
theorem actual_gauss_field_le_output_field
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    projectiveRatioField (K := K) (rationalImageNormal H I.equation)
      (imageNormalPivot H I) ≤ polynomialOutputField H := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  exact (polynomialOutputField H).div_mem
    (imageRelationNormal_mem_fullOutputField H I.equation i)
    (imageRelationNormal_mem_fullOutputField H I.equation (imageNormalPivot H I))

/-- Adjoining the actual outputs over the Gauss field gives exactly
the original output field after restricting coefficients. -/
theorem actual_gauss_adjoin_outputs_restrictScalars
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H) :
    (IntermediateField.adjoin
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (Set.range (fun i => algebraMap (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K)) (H i)))).restrictScalars K =
      polynomialOutputField H := by
  rw [IntermediateField.restrictScalars_adjoin_eq_sup]
  exact sup_eq_right.mpr (actual_gauss_field_le_output_field H I)

variable [CharZero K]

/-- In rank three and Gauss dimension one, exactly two algebraically
independent output parameters remain over the actual Gauss field. -/
theorem actual_gauss_fiber_output_trdeg_two
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1) :
    Algebra.trdeg
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (IntermediateField.adjoin
        (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
        (Set.range (fun i => algebraMap (MvPolynomial (Fin 4) K)
          (FractionRing (MvPolynomial (Fin 4) K)) (H i)))) = 2 := by
  let M := projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
  let J := IntermediateField.adjoin M (Set.range (fun i => algebraMap (MvPolynomial (Fin 4) K)
    (FractionRing (MvPolynomial (Fin 4) K)) (H i)))
  let : FaithfulSMul K M :=
    (faithfulSMul_iff_algebraMap_injective K M).mpr (algebraMap K M).injective
  let : FaithfulSMul M J :=
    (faithfulSMul_iff_algebraMap_injective M J).mpr (algebraMap M J).injective
  have hM : Algebra.trdeg K M = 1 := hGauss
  have hJ : Algebra.trdeg K J = 3 := by
    change Algebra.trdeg K (J.restrictScalars K) = 3
    rw [actual_gauss_adjoin_outputs_restrictScalars H I, polynomialOutputField_trdeg_eq_rank, hrank]
    norm_num
  have he := trdeg_add_eq (A := J) K M
  rw [hM, hJ] at he
  have hle : Algebra.trdeg M J ≤ 3 := le_add_self.trans_eq he
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (hle.trans_lt (by simp))
  rw [hn] at he
  have hn' : 1 + n = 3 := by exact_mod_cast he
  have hn2 : n = 2 := by omega
  change Algebra.trdeg M J = 2
  rw [hn, hn2]
  rfl

end DimensionFourDependence
