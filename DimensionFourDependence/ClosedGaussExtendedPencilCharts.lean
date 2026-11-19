import DimensionFourDependence.ClosedGaussPencilCharts
import Mathlib.RingTheory.FiniteStability

/-! # Finite normalization of the actual pencil charts after base extension

The charts remain domains under every algebraic coefficient extension.
Their normalization is formed after that extension, rather than assumed
to be a base change of the original normalization. This is the order of
operations required for the normalized pencil in Lemma 4.2.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]

/-- Every algebraic coefficient extension preserves the actual projective
pencil chart as a domain. -/
theorem actual_closed_gauss_extended_chart_isDomain
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (s : Fin 4 ≃ Option (Fin 3))
    (E : Type*) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E] :
    IsDomain (E ⊗[closedGaussParameterField H I] closedGaussPencilChartAlgebra H I s) := by
  let C := closedGaussParameterField H I
  let A := closedGaussPencilChartAlgebra H I s
  let : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  let : IsDomain (A ⊗[C] E) := subalgebra_algebraic_base_change_isDomain
    (closedGaussParameterField_relatively_closed H I) A
  let c := Algebra.TensorProduct.comm C E A
  exact Function.Injective.isDomain c c.injective

/-- Normalizing each actual projective pencil chart after an algebraic
coefficient extension gives a finite ring extension. -/
theorem actual_closed_gauss_extended_chart_normalization_finite
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (s : Fin 4 ≃ Option (Fin 3))
    (E : Type*) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E] :
    Module.Finite (E ⊗[closedGaussParameterField H I] closedGaussPencilChartAlgebra H I s)
      (normalizationRing (E ⊗[closedGaussParameterField H I] closedGaussPencilChartAlgebra H I s)) := by
  let C := closedGaussParameterField H I
  let A := closedGaussPencilChartAlgebra H I s
  let : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap C E).injective
  let : Algebra.FiniteType C A := closedGaussPencilChartAlgebra_finiteType H I s
  let : IsDomain (E ⊗[C] A) := actual_closed_gauss_extended_chart_isDomain H I s E
  exact normalizationRing_finite _ (K := E)

/-- The actual chart normalized after coefficient extension is normal. -/
theorem actual_closed_gauss_extended_chart_normalization_normal
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (s : Fin 4 ≃ Option (Fin 3))
    (E : Type*) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E] :
    IsIntegrallyClosed (normalizationRing
      (E ⊗[closedGaussParameterField H I] closedGaussPencilChartAlgebra H I s)) := by
  let : IsDomain (E ⊗[closedGaussParameterField H I] closedGaussPencilChartAlgebra H I s) :=
    actual_closed_gauss_extended_chart_isDomain H I s E
  exact normalizationRing_isIntegrallyClosed _

/-- Normalizing after coefficient extension preserves that chart's
fraction field. -/
theorem actual_closed_gauss_extended_chart_normalization_fraction_field
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (s : Fin 4 ≃ Option (Fin 3))
    (E : Type*) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E] :
    IsFractionRing (normalizationRing
      (E ⊗[closedGaussParameterField H I] closedGaussPencilChartAlgebra H I s))
      (FractionRing (E ⊗[closedGaussParameterField H I] closedGaussPencilChartAlgebra H I s)) := by
  let : IsDomain (E ⊗[closedGaussParameterField H I] closedGaussPencilChartAlgebra H I s) :=
    actual_closed_gauss_extended_chart_isDomain H I s E
  exact normalizationRing_isFractionRing _

end DimensionFourDependence
