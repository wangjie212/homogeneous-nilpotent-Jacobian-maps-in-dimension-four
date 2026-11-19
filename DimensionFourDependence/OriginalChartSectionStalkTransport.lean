import DimensionFourDependence.OriginalChartCanonicalSectionOrder
import DimensionFourDependence.LocalEquivOrderTransport

/-! # The original normalized section coefficient in an identified geometric stalk -/

namespace DimensionFourDependence

variable {k A C : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A] [CommRing C]

/-- The actual regular stalk coefficient supplied by the original
normalization coefficient and the given normalization-chart stalk
isomorphism. -/
noncomputable def originalChartSectionStalkGerm
    (Q : Ideal (normalizationRing A)) [Q.IsPrime]
    (β : C ≃+* Localization.AtPrime Q)
    (c : Fin 3 → A) (x : Fin 4 → FractionRing A)
    (sectionValue : ProjectiveNormalizedSection (k := k) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hratios : (fun i => x (s.symm (some i)) / x (s.symm none)) =
      (fun i => algebraMap A (FractionRing A) (c i))) : C :=
  β.symm (algebraMap (normalizationRing A) (Localization.AtPrime Q)
    (originalChartSectionNormalizationCoefficient c x sectionValue s hbase hratios))

/-- The original normalized section germ retains its exact canonical
local coefficient under the actual chart-stalk identification. -/
theorem original_chart_section_stalk_germ_local_value
    (Q : Ideal (normalizationRing A)) [Q.IsPrime]
    (β : C ≃+* Localization.AtPrime Q)
    (c : Fin 3 → A) (x : Fin 4 → FractionRing A)
    (sectionValue : ProjectiveNormalizedSection (k := k) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hratios : (fun i => x (s.symm (some i)) / x (s.symm none)) =
      (fun i => algebraMap A (FractionRing A) (c i))) :
    β (originalChartSectionStalkGerm Q β c x sectionValue s hbase hratios) =
      algebraMap (normalizationRing A) (Localization.AtPrime Q)
        (originalChartSectionNormalizationCoefficient c x sectionValue s hbase hratios) :=
  β.apply_symm_apply _

variable [IsLocalRing C]

/-- Original normalized section orders in the identified actual stalk
are exactly the orders of its canonical coefficient in the original
normalization-prime localization. -/
theorem original_chart_section_stalk_order_iff
    (Q : Ideal (normalizationRing A)) [Q.IsPrime]
    (β : C ≃+* Localization.AtPrime Q)
    (c : Fin 3 → A) (x : Fin 4 → FractionRing A)
    (sectionValue : ProjectiveNormalizedSection (k := k) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hratios : (fun i => x (s.symm (some i)) / x (s.symm none)) =
      (fun i => algebraMap A (FractionRing A) (c i))) (a : ℕ) :
    originalChartSectionStalkGerm Q β c x sectionValue s hbase hratios ∈
        (IsLocalRing.maximalIdeal C) ^ a ↔
      algebraMap (normalizationRing A) (Localization.AtPrime Q)
        (originalChartSectionNormalizationCoefficient c x sectionValue s hbase hratios) ∈
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a := by
  have h := local_equiv_maximalIdeal_pow_mem_iff (A := C) (B := Localization.AtPrime Q) β
    (originalChartSectionStalkGerm Q β c x sectionValue s hbase hratios) a
  rw [original_chart_section_stalk_germ_local_value] at h
  exact h.symm

end DimensionFourDependence
