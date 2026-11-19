import DimensionFourDependence.OriginalChartSectionCoefficient
import DimensionFourDependence.ConstructedOriginalSectionBound

/-! # The canonical original section coefficient satisfies the degree bound

Its canonical normalization coefficient constructs the actual local
value. No independent local element or equality of rational values is
supplied to the section bound.
-/

namespace DimensionFourDependence

universe u

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k A : Type u} [Field k] [CharZero k]
  [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]

/-- The canonical normalization-local value of a nonzero original-chart
section coefficient has order bounded by the original equation degree.
Its local realization, projection and every auxiliary scalar action are
constructed from the original coordinates. -/
theorem canonical_original_normalization_section_order_le_equation_degree
    (c : Fin 3 → A) (hc : Algebra.adjoin k (Set.range c) = ⊤)
    (htr : 2 ≤ Algebra.trdeg k A)
    (f : MvPolynomial (Fin 3) k) (hf : f ≠ 0) (hroot : aeval c f = 0)
    (Q : Ideal (normalizationRing A)) [Q.IsPrime] (hQ : Q.height = 1)
    (x : Fin 4 → FractionRing A) (sectionValue : ProjectiveNormalizedSection (k := k) x)
    (s : Fin 4 ≃ Option (Fin 3)) (hbase : x (s.symm none) ≠ 0)
    (hratios : (fun i => x (s.symm (some i)) / x (s.symm none)) =
      (fun i => algebraMap A (FractionRing A) (c i)))
    (hsection : (sectionValue.coefficient (s.symm none) : FractionRing A) ≠ 0)
    (a : ℕ) (horder : algebraMap (normalizationRing A) (Localization.AtPrime Q)
      (originalChartSectionNormalizationCoefficient c x sectionValue s hbase hratios) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a) : a ≤ f.totalDegree := by
  let B := Localization.AtPrime Q
  let L := FractionRing A
  let : Algebra B L := normalizationPrimeFractionAlgebra Q
  let b : B := algebraMap (normalizationRing A) B
    (originalChartSectionNormalizationCoefficient c x sectionValue s hbase hratios)
  have hvalue : algebraMap B L b = (sectionValue.coefficient (s.symm none) : L) :=
    original_chart_section_normalization_local_value c x sectionValue s hbase hratios Q
  have hb : b ≠ 0 := by
    intro hz
    apply hsection
    rw [← hvalue, hz, map_zero]
  exact canonical_original_section_order_le_original_equation_degree
    c hc htr f hf hroot Q hQ x sectionValue s hbase hratios b hb a horder hvalue.symm

end DimensionFourDependence
