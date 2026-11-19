import DimensionFourDependence.ProjectiveNormalizedSection
import DimensionFourDependence.NormalizationPrimeFunctionField

/-! # The actual original affine normalization contains the section coefficient

The original chart ratios take their specified original affine values.
Every valuation ring containing the affine algebra therefore contains
the section coefficient, so it belongs to that algebra's actual integral
closure. Localizing this canonical coefficient supplies the local value
in the actual normalization-prime stalk.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k A L : Type*} [Field k] [CommRing A] [Algebra k A]
  [Field L] [Algebra k L] [Algebra A L] [IsScalarTower k A L]

/-- The original affine values of the original chart ratios make its
normalized section coefficient integral over that entire affine algebra. -/
theorem original_chart_section_coefficient_isIntegral
    (c : Fin 3 → A) (x : Fin 4 → L)
    (sectionValue : ProjectiveNormalizedSection (k := k) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hratios : (fun i => x (s.symm (some i)) / x (s.symm none)) =
      (fun i => algebraMap A L (c i))) :
    IsIntegral A (sectionValue.coefficient (s.symm none) : L) := by
  apply isIntegral_of_mem_all_valuationSubrings
  intro V hA
  apply projective_normalized_section_original_chart_mem_valuation x sectionValue V
  · intro z
    rw [IsScalarTower.algebraMap_apply k A L]
    exact hA (algebraMap k A z)
  · intro i
    obtain ⟨j, rfl⟩ := s.symm.surjective i
    cases j with
    | none =>
      rw [div_self hbase]
      exact V.one_mem
    | some j =>
      rw [congrFun hratios j]
      exact hA (c j)

variable [IsDomain A]

/-- The section's actual coefficient in the canonical normalization of
the original affine ring, with its original rational value. -/
noncomputable def originalChartSectionNormalizationCoefficient
    (c : Fin 3 → A) (x : Fin 4 → FractionRing A)
    (sectionValue : ProjectiveNormalizedSection (k := k) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hratios : (fun i => x (s.symm (some i)) / x (s.symm none)) =
      (fun i => algebraMap A (FractionRing A) (c i))) : normalizationRing A :=
  ⟨(sectionValue.coefficient (s.symm none) : FractionRing A),
    original_chart_section_coefficient_isIntegral c x sectionValue s hbase hratios⟩

/-- The normalization-prime local inclusion preserves the entire actual
normalization, in addition to the original affine ring. -/
theorem normalization_prime_local_normalization_value
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (z : normalizationRing A) :
    let : Algebra (Localization.AtPrime Q) (FractionRing A) := normalizationPrimeFractionAlgebra Q
    algebraMap (Localization.AtPrime Q) (FractionRing A)
      (algebraMap (normalizationRing A) (Localization.AtPrime Q) z) = (z : FractionRing A) := by
  let : IsFractionRing (normalizationRing A) (FractionRing A) := normalizationRing_isFractionRing A
  let : FaithfulSMul (normalizationRing A) (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (normalizationRing A) (FractionRing A))
  exact primeLocalizationFractionHom_algebraMap Q z

/-- Localizing the canonical original-chart section coefficient gives
its same rational value in the original affine function field. -/
theorem original_chart_section_normalization_local_value
    (c : Fin 3 → A) (x : Fin 4 → FractionRing A)
    (sectionValue : ProjectiveNormalizedSection (k := k) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hratios : (fun i => x (s.symm (some i)) / x (s.symm none)) =
      (fun i => algebraMap A (FractionRing A) (c i)))
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] :
    let : Algebra (Localization.AtPrime Q) (FractionRing A) := normalizationPrimeFractionAlgebra Q
    algebraMap (Localization.AtPrime Q) (FractionRing A)
      (algebraMap (normalizationRing A) (Localization.AtPrime Q)
        (originalChartSectionNormalizationCoefficient c x sectionValue s hbase hratios)) =
      (sectionValue.coefficient (s.symm none) : FractionRing A) :=
  normalization_prime_local_normalization_value Q _

end DimensionFourDependence
