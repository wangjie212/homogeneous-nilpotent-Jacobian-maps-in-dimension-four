import DimensionFourDependence.ExtendedGaussRatioCoordinates
import DimensionFourDependence.ProjectivePencilFunctionField
import DimensionFourDependence.ProjectiveSourceCoordinates

/-! # The extended chart maps retain the original source functions

The tensor chart inclusion and the actual extended generic-point ratio
evaluation agree on every original source polynomial. Their induced
normalization isomorphism retains these same functions.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "x₀" => rationalCoordinate (K := K) (n := 4)
local notation "zₑ" => primeQuotientCoordinate (extendedClosedGaussPencilIdeal H I E)
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K) x₀ (s.symm none)
local notation "S₀" => projectiveCoordinateChartAlgebra (C := C₀) x₀ (s.symm none)
local notation "Sₑ" => projectiveCoordinateChartAlgebra (C := E) zₑ (s.symm none)

/-- The original projective source includes in the tensor chart through
its original pencil-chart functions. -/
noncomputable def extendedClosedGaussTensorSourceHom : R₀ →+* S₀ ⊗[C₀] E :=
  (Algebra.TensorProduct.includeLeft : S₀ →ₐ[C₀] S₀ ⊗[C₀] E).toRingHom.comp
    (projectivePencilBaseInclusion H I s).toRingHom

/-- Original source polynomials evaluated at the actual extended ratios,
with their coefficients mapped through the original closed parameter field. -/
noncomputable def extendedClosedGaussSourcePolynomialHom :
    MvPolynomial (Fin 3) K →+* Sₑ :=
  MvPolynomial.eval₂Hom
    ((algebraMap E Sₑ).comp ((algebraMap C₀ E).comp (algebraMap K C₀)))
    (fun i => projectiveChartTransition (C := E) zₑ (s.symm none) (s.symm (some i)))

/-- The tensor chart inclusion sends each original coordinate ratio to
its actual extended source value under the chart isomorphism. -/
theorem extendedClosedGaussTensorSourceHom_ratio (i : Fin 4) :
    extendedClosedGaussRatioCoordinateEquiv H I E hH e s
      (extendedClosedGaussTensorSourceHom H I E s
        (projectiveChartTransition (C := K) x₀ (s.symm none) i)) =
      projectiveChartTransition (C := E) zₑ (s.symm none) i :=
  extendedClosedGaussRatioCoordinateEquiv_tmul_ratio H I E hH e s i

/-- The original coefficient map is the actual composite coefficient
map in the extended chart. -/
theorem extendedClosedGaussTensorSourceHom_coefficient (c : K) :
    extendedClosedGaussRatioCoordinateEquiv H I E hH e s
      (extendedClosedGaussTensorSourceHom H I E s (algebraMap K R₀ c)) =
      algebraMap E Sₑ (algebraMap C₀ E (algebraMap K C₀ c)) := by
  change extendedClosedGaussRatioCoordinateEquiv H I E hH e s
    ((algebraMap C₀ S₀ (algebraMap K C₀ c)) ⊗ₜ[C₀] (1 : E)) = _
  have ht : (algebraMap C₀ S₀ (algebraMap K C₀ c)) ⊗ₜ[C₀] (1 : E) =
      (1 : S₀) ⊗ₜ[C₀] algebraMap C₀ E (algebraMap K C₀ c) := by
    simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul]
  rw [ht]
  exact extendedClosedGaussRatioCoordinateEquiv_tmul_coefficient H I E hH e s _

/-- The two source-chart maps agree on every original polynomial, not
just on the chosen coordinate generators. -/
theorem extendedClosedGaussTensorSourceHom_polynomial (P : MvPolynomial (Fin 3) K) :
    extendedClosedGaussRatioCoordinateEquiv H I E hH e s
      (extendedClosedGaussTensorSourceHom H I E s
        (projectiveSourceFullChartCoordinateEquiv s P)) =
      extendedClosedGaussSourcePolynomialHom H I E s P := by
  let f : MvPolynomial (Fin 3) K →+* Sₑ :=
    (extendedClosedGaussRatioCoordinateEquiv H I E hH e s).toRingHom.comp
      ((extendedClosedGaussTensorSourceHom H I E s).comp
        (projectiveSourceFullChartCoordinateEquiv (K := K) s).toRingHom)
  have hf : f = extendedClosedGaussSourcePolynomialHom H I E s := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change extendedClosedGaussRatioCoordinateEquiv H I E hH e s
        (extendedClosedGaussTensorSourceHom H I E s
          (projectiveSourceFullChartCoordinateEquiv s (C c))) = _
      rw [show (C c : MvPolynomial (Fin 3) K) = algebraMap K _ c from rfl,
        (projectiveSourceFullChartCoordinateEquiv (K := K) s).commutes]
      simpa only [extendedClosedGaussSourcePolynomialHom, MvPolynomial.algebraMap_eq,
        eval₂Hom_C, RingHom.comp_apply] using
        extendedClosedGaussTensorSourceHom_coefficient H I E hH e s c
    · intro i
      have hx : projectiveSourceFullChartCoordinateEquiv (K := K) s (X i) =
          projectiveChartTransition (C := K) x₀ (s.symm none) (s.symm (some i)) := by
        apply Subtype.ext
        rw [projectiveSourceFullChartCoordinateEquiv_source, aeval_X]
        rfl
      change extendedClosedGaussRatioCoordinateEquiv H I E hH e s
        (extendedClosedGaussTensorSourceHom H I E s
          (projectiveSourceFullChartCoordinateEquiv s (X i))) = _
      rw [hx]
      simpa only [extendedClosedGaussSourcePolynomialHom, eval₂Hom_X'] using
        extendedClosedGaussTensorSourceHom_ratio H I E hH e s (s.symm (some i))
  exact RingHom.congr_fun hf P

/-- The normalization coordinate isomorphism preserves every element
of the original tensor chart through its specified source map. -/
theorem extendedClosedGaussNormalizedRatioCoordinateEquiv_algebraMap
    (r : S₀ ⊗[C₀] E) :
    extendedClosedGaussNormalizedRatioCoordinateEquiv H I E hH e s
      (algebraMap (S₀ ⊗[C₀] E) (normalizationRing (S₀ ⊗[C₀] E)) r) =
      algebraMap Sₑ (normalizationRing Sₑ)
        (extendedClosedGaussRatioCoordinateEquiv H I E hH e s r) := by
  unfold extendedClosedGaussNormalizedRatioCoordinateEquiv
  exact normalizationCoordinateEquiv_algebraMap _ r

/-- In the actual normalized extended ratio ring, the original source
polynomial has the same value as in the canonical tensor normalization. -/
theorem extendedClosedGaussNormalizedRatioCoordinateEquiv_source_polynomial
    (P : MvPolynomial (Fin 3) K) :
    extendedClosedGaussNormalizedRatioCoordinateEquiv H I E hH e s
      (algebraMap (S₀ ⊗[C₀] E) (normalizationRing (S₀ ⊗[C₀] E))
        (extendedClosedGaussTensorSourceHom H I E s
          (projectiveSourceFullChartCoordinateEquiv s P))) =
      algebraMap Sₑ (normalizationRing Sₑ)
        (extendedClosedGaussSourcePolynomialHom H I E s P) := by
  rw [extendedClosedGaussNormalizedRatioCoordinateEquiv_algebraMap,
    extendedClosedGaussTensorSourceHom_polynomial]

end DimensionFourDependence
