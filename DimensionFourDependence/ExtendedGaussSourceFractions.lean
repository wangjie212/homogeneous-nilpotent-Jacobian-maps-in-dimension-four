import DimensionFourDependence.ProjectiveCoefficientChartMaps
import DimensionFourDependence.ExtendedGaussSourceMorphism
import DimensionFourDependence.ExtendedGaussSourceNormalization

/-! # Original projective fractions and the extended source-coordinate map

The source map used by the tensor-normalization local models agrees
with the actual coefficient map on every homogeneous source fraction.
-/

namespace DimensionFourDependence

open MvPolynomial HomogeneousLocalization
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Every original source variable is nonzero in the original rational
source field. -/
theorem source_rationalCoordinate_ne_zero {K : Type*} [Field K] {n : ℕ} (a : Fin n) :
    rationalCoordinate (K := K) (n := n) a ≠ 0 := by
  simpa only [rationalCoordinate, map_zero] using
    (IsFractionRing.injective (MvPolynomial (Fin n) K)
      (FractionRing (MvPolynomial (Fin n) K))).ne (X_ne_zero a)

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
local notation "Sₑ" => projectiveCoordinateChartAlgebra (C := E) zₑ (s.symm none)

include hH e

/-- Actual extended source evaluation sends each original projective
coordinate ratio to the same original ratio over the new coefficients. -/
theorem extendedClosedGaussSourceChartHom_ratio (i : Fin 4) :
    extendedClosedGaussSourceChartHom H I E s
      (projectiveChartTransition (C := K) x₀ (s.symm none) i) =
      projectiveChartTransition (C := E) zₑ (s.symm none) i :=
  (extendedClosedGaussSourceChartHom_compatibility H I E hH e s _).symm.trans
    (extendedClosedGaussTensorSourceHom_ratio H I E hH e s i)

/-- Actual extended source evaluation retains the specified original
coefficient map through the closed parameter field. -/
theorem extendedClosedGaussSourceChartHom_coefficient (c : K) :
    extendedClosedGaussSourceChartHom H I E s (algebraMap K R₀ c) =
      algebraMap E Sₑ (extendedClosedGaussSourceCoefficientHom H I E c) :=
  (extendedClosedGaussSourceChartHom_compatibility H I E hH e s _).symm.trans
    (extendedClosedGaussTensorSourceHom_coefficient H I E hH e s c)

/-- Evaluating any original four-variable polynomial at its source
ratios agrees with evaluation at the actual extended source ratios. -/
theorem extendedClosedGaussSourceChartHom_aeval_ratios
    (P : MvPolynomial (Fin 4) K) :
    extendedClosedGaussSourceChartHom H I E s
      (aeval (fun i => projectiveChartTransition (C := K) x₀ (s.symm none) i) P) =
      MvPolynomial.eval₂Hom
        ((algebraMap E Sₑ).comp (extendedClosedGaussSourceCoefficientHom H I E))
        (fun i => projectiveChartTransition (C := E) zₑ (s.symm none) i) P := by
  let ν : MvPolynomial (Fin 4) K →+* Sₑ := MvPolynomial.eval₂Hom
    ((algebraMap E Sₑ).comp (extendedClosedGaussSourceCoefficientHom H I E))
    (fun i => projectiveChartTransition (C := E) zₑ (s.symm none) i)
  have heq : (extendedClosedGaussSourceChartHom H I E s).comp
        (aeval (fun i => projectiveChartTransition (C := K) x₀ (s.symm none) i)).toRingHom = ν := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change extendedClosedGaussSourceChartHom H I E s
        (aeval (fun i => projectiveChartTransition (C := K) x₀ (s.symm none) i) (C c)) = ν (C c)
      simp only [ν, aeval_C, eval₂Hom_C, RingHom.comp_apply]
      exact extendedClosedGaussSourceChartHom_coefficient H I E hH e s c
    · intro i
      change extendedClosedGaussSourceChartHom H I E s
        (aeval (fun i => projectiveChartTransition (C := K) x₀ (s.symm none) i) (X i)) = ν (X i)
      simp only [ν, aeval_X, eval₂Hom_X']
      exact extendedClosedGaussSourceChartHom_ratio H I E hH e s i
  exact RingHom.congr_fun heq P

/-- On every actual homogeneous fraction, the original source map of
the tensor local models agrees with the actual coefficient-extension map. -/
theorem extendedClosedGaussSourceChartHom_homogeneous_fraction
    (w : Away (homogeneousSubmodule (Fin 4) K) (X (s.symm none))) :
    extendedClosedGaussSourceChartHom H I E s
      (homogeneousCoordinateChartToSource (C := K) x₀ (s.symm none)
        (source_rationalCoordinate_ne_zero _) w) =
      homogeneousCoordinateChartToSource (C := E) zₑ (s.symm none)
        (extendedClosedGaussRatioCoordinate_ne_zero H I E _)
        (polynomialCoefficientAwayHom (extendedClosedGaussSourceCoefficientHom H I E) (s.symm none) w) := by
  obtain ⟨n, P, hP, rfl⟩ := Away.mk_surjective (homogeneousSubmodule (Fin 4) K)
    (isHomogeneous_X (R := K) (s.symm none)) w
  have horig : homogeneousCoordinateChartToSource (C := K) x₀ (s.symm none)
      (source_rationalCoordinate_ne_zero _) (Away.mk _ (isHomogeneous_X (R := K) _) n P hP) =
      aeval (fun i => projectiveChartTransition (C := K) x₀ (s.symm none) i) P := by
    apply Subtype.ext
    change homogeneousCoordinateChartEval x₀ (s.symm none) _ _ = _
    rw [homogeneousCoordinateChartEval_mk_normalized]
    exact (MvPolynomial.comp_aeval_apply
      (fun i => projectiveChartTransition (C := K) x₀ (s.symm none) i) (R₀).val P).symm
  rw [polynomialCoefficientAwayHom_mk, horig,
    extendedClosedGaussSourceChartHom_aeval_ratios H I E hH e s P]
  apply Subtype.ext
  change ((Sₑ).val.toRingHom.comp (MvPolynomial.eval₂Hom
      ((algebraMap E Sₑ).comp (extendedClosedGaussSourceCoefficientHom H I E))
      (fun i => projectiveChartTransition (C := E) zₑ (s.symm none) i))) P =
    homogeneousCoordinateChartEval zₑ (s.symm none) _ _
  have heq : (Sₑ).val.toRingHom.comp (MvPolynomial.eval₂Hom
        ((algebraMap E Sₑ).comp (extendedClosedGaussSourceCoefficientHom H I E))
        (fun i => projectiveChartTransition (C := E) zₑ (s.symm none) i)) =
      (aeval (fun i => zₑ i / zₑ (s.symm none))).toRingHom.comp
        (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, eval₂Hom_C, MvPolynomial.map_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      rfl
    · intro i
      simp only [RingHom.comp_apply, eval₂Hom_X', MvPolynomial.map_X,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rfl
  exact (RingHom.congr_fun heq P).trans
    (homogeneousCoordinateChartEval_mk_normalized zₑ (s.symm none)
      (extendedClosedGaussRatioCoordinate_ne_zero H I E _) n
      (MvPolynomial.map (extendedClosedGaussSourceCoefficientHom H I E) P) (hP.map _)).symm

end DimensionFourDependence
