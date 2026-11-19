import DimensionFourDependence.NormalizedCurveEtaleOpen
import DimensionFourDependence.RationalClosedGaussCover

/-! # An actual etale-open model for finite covers of the closed Gauss field

The original dimension-one Gauss image constructs its rational closed
parameter field. For every finite extension of that field, this module
constructs the finite normalized affine parameter curve and a nonzero
original parameter polynomial over whose basic open the cover is etale.
-/

namespace DimensionFourDependence

variable {K : Type*} [Field K] [CharZero K]

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

/-- The original Gauss image and an arbitrary actual finite extension of
its closed parameter field supply a finite normalized curve model and
an actual nonempty etale parameter open, as required in Lemma 4.2. -/
theorem actual_closed_gauss_finite_cover_etale_parameter_open
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (E : Type*) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Module.Finite (closedGaussParameterField H I) E] :
    ∃ e : RatFunc K ≃ₐ[K] closedGaussParameterField H I,
      letI : Algebra (RatFunc K) E :=
        ((algebraMap (closedGaussParameterField H I) E).comp e.toRingHom).toAlgebra
      letI : Algebra (Polynomial K) E :=
        ((algebraMap (RatFunc K) E).comp (algebraMap (Polynomial K) (RatFunc K))).toAlgebra
      ∃ a : Polynomial K, a ≠ 0 ∧
        Module.Finite (Polynomial K) (integralClosure (Polynomial K) E) ∧
        Algebra.Etale (Polynomial K)
          (Localization.Away (algebraMap (Polynomial K) (integralClosure (Polynomial K) E) a)) := by
  obtain ⟨e⟩ := actual_closed_gauss_parameter_rational_function_field H I hGauss
  refine ⟨e, ?_⟩
  let C := closedGaussParameterField H I
  let : Algebra (RatFunc K) C := e.toRingHom.toAlgebra
  let : Module.Finite (RatFunc K) C :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) C) e.surjective
  let : Algebra (RatFunc K) E := ((algebraMap C E).comp e.toRingHom).toAlgebra
  let : IsScalarTower (RatFunc K) C E := IsScalarTower.of_algebraMap_eq (by intro r; rfl)
  let : Module.Finite (RatFunc K) E := Module.Finite.trans (R := RatFunc K) C E
  exact finite_rational_parameter_cover_etale_open (K₀ := K) (E₀ := E)

end DimensionFourDependence
