import DimensionFourDependence.OriginalChartSectionStalkTransport

/-! # Nonzero original normalized-frame coefficients give nonzero actual stalk germs -/

namespace DimensionFourDependence

variable {k A C : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A] [CommRing C]

/-- The actual geometric stalk germ of a nonzero original normalized
coefficient is nonzero. Its canonical local value retains the original
rational function, so no independent nonvanishing hypothesis is needed. -/
theorem original_chart_section_stalk_germ_ne_zero
    (Q : Ideal (normalizationRing A)) [Q.IsPrime]
    (β : C ≃+* Localization.AtPrime Q)
    (c : Fin 3 → A) (x : Fin 4 → FractionRing A)
    (sectionValue : ProjectiveNormalizedSection (k := k) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hratios : (fun i => x (s.symm (some i)) / x (s.symm none)) =
      (fun i => algebraMap A (FractionRing A) (c i)))
    (hsection : (sectionValue.coefficient (s.symm none) : FractionRing A) ≠ 0) :
    originalChartSectionStalkGerm Q β c x sectionValue s hbase hratios ≠ 0 := by
  let : Algebra (Localization.AtPrime Q) (FractionRing A) := normalizationPrimeFractionAlgebra Q
  intro hz
  have hlocal := original_chart_section_stalk_germ_local_value Q β c x sectionValue s hbase hratios
  have hzero : algebraMap (normalizationRing A) (Localization.AtPrime Q)
      (originalChartSectionNormalizationCoefficient c x sectionValue s hbase hratios) = 0 :=
    hlocal.symm.trans ((congrArg β hz).trans (map_zero β))
  have hvalue := original_chart_section_normalization_local_value c x sectionValue s hbase hratios Q
  apply hsection
  rw [← hvalue, hzero, map_zero]

end DimensionFourDependence
