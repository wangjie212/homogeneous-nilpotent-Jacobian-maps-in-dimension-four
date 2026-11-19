import DimensionFourDependence.ExtendedGaussPencilPrime
import DimensionFourDependence.ProjectiveCoefficientChartEquiv
import DimensionFourDependence.NormalizationCoordinateEquiv

/-! # Original tensor ratio rings are the extended pencil's actual coordinates

The actual extended pencil generic point has precisely the extended
original source equations. Dehomogenization identifies each of its ratio
rings with the existing original ratio ring tensor the new field. The
canonical normalization rings are then identified in their own fraction fields.
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

local notation "C₀" => closedGaussParameterField H I
local notation "Pₑ" => extendedClosedGaussPencilIdeal H I E
local notation "zₑ" => primeQuotientCoordinate Pₑ
local notation "S₀" s:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm s none)
local notation "Sₑ" s:max => projectiveCoordinateChartAlgebra (C := E) zₑ (Equiv.symm s none)

/-- The canonical extended generic source coordinates are nonzero in
their original coordinate order. -/
theorem extendedClosedGaussRatioCoordinate_ne_zero (a : Fin 4) : zₑ a ≠ 0 := by
  let : (extendCoefficientIdeal E (fiberVanishingIdeal (L := C₀)
      (rationalCoordinate (K := K) (n := 4)))).IsPrime := extendedClosedGaussPencilIdeal_isPrime H I E
  exact extended_prime_quotient_coordinate_ne_zero
    (C := C₀) (E := E) (rationalCoordinate (K := K) (n := 4)) a
    (extendedClosedGaussPencilIdeal_X_not_mem H I E a)

/-- The actual extended ratio coordinates have exactly the extended
homogeneous source prime as their full polynomial relation ideal. -/
theorem extendedClosedGaussRatioCoordinate_relations :
    RingHom.ker (aeval zₑ).toRingHom = Pₑ :=
  primeQuotientCoordinate_relations Pₑ

include hH e in
/-- The extended ratio chart admits an isomorphism preserving all of
the original source ratios, as an algebra over the extended field. -/
theorem exists_extendedClosedGaussCoefficientChartEquiv (s : Fin 4 ≃ Option (Fin 3)) :
    ∃ b : E ⊗[C₀] S₀ s ≃ₐ[E] Sₑ s, ∀ i : Fin 4,
      b ((1 : E) ⊗ₜ[C₀]
        projectiveChartTransition (C := C₀) (rationalCoordinate (K := K) (n := 4))
          (s.symm none) i) = projectiveChartTransition (C := E) zₑ (s.symm none) i := by
  classical
  obtain ⟨p, q, D, _, _, hq, hpH, hqH, hrel, ht⟩ :=
    actual_closed_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  have hG := (actual_closed_gauss_pencil_homogeneous_degree H I e p q hq hrel hpH hqH).2.1
  have hker : RingHom.ker (aeval (rationalCoordinate (K := K) (n := 4)) :
      MvPolynomial (Fin 4) C₀ →ₐ[C₀] FractionRing (MvPolynomial (Fin 4) K)).toRingHom =
      Ideal.span {closedGaussPencilEquation H I e p q} :=
    actual_closed_gauss_pencil_relation_ideal H I e p q hq hrel ht
  have ha : rationalCoordinate (K := K) (s.symm none) ≠ 0 := by
    simpa only [rationalCoordinate, map_zero] using
      (IsFractionRing.injective (MvPolynomial (Fin 4) K)
        (FractionRing (MvPolynomial (Fin 4) K))).ne (X_ne_zero (s.symm none))
  let : (extendCoefficientIdeal E (fiberVanishingIdeal (L := C₀)
      (rationalCoordinate (K := K) (n := 4)))).IsPrime := extendedClosedGaussPencilIdeal_isPrime H I E
  let b := projectiveCoefficientChartEquiv (C := C₀) (E := E)
    (rationalCoordinate (K := K) (n := 4)) (closedGaussPencilEquation H I e p q) hG hker s ha
    (extendedClosedGaussPencilIdeal_X_not_mem H I E (s.symm none))
  exact ⟨b, fun i => projectiveCoefficientChartEquiv_tmul_ratio
    (C := C₀) (E := E) (rationalCoordinate (K := K) (n := 4))
    (closedGaussPencilEquation H I e p q) hG hker s ha
    (extendedClosedGaussPencilIdeal_X_not_mem H I E (s.symm none)) i⟩

/-- A coefficient-linear extended chart identification, chosen together
with its original source-ratio compatibility proof. -/
noncomputable def extendedClosedGaussCoefficientChartEquiv (s : Fin 4 ≃ Option (Fin 3)) :
    E ⊗[C₀] S₀ s ≃ₐ[E] Sₑ s :=
  (exists_extendedClosedGaussCoefficientChartEquiv H I E hH e s).choose

/-- The chosen coefficient-linear chart identification preserves every
original source coordinate ratio. -/
theorem extendedClosedGaussCoefficientChartEquiv_tmul_ratio
    (s : Fin 4 ≃ Option (Fin 3)) (i : Fin 4) :
    extendedClosedGaussCoefficientChartEquiv H I E hH e s
      ((1 : E) ⊗ₜ[C₀]
        projectiveChartTransition (C := C₀) (rationalCoordinate (K := K) (n := 4))
          (s.symm none) i) = projectiveChartTransition (C := E) zₑ (s.symm none) i :=
  (exists_extendedClosedGaussCoefficientChartEquiv H I E hH e s).choose_spec i

/-- The original tensor chart, in the order used by the local models,
is the actual ratio algebra of the extended pencil generic point. -/
noncomputable def extendedClosedGaussRatioCoordinateEquiv (s : Fin 4 ≃ Option (Fin 3)) :
    S₀ s ⊗[C₀] E ≃+* Sₑ s :=
  (Algebra.TensorProduct.comm C₀ (S₀ s) E).toRingEquiv.trans
    (extendedClosedGaussCoefficientChartEquiv H I E hH e s).toRingEquiv

/-- In the tensor order of the local normalization models, the original
ratio still maps to its actual extended generic-source ratio. -/
theorem extendedClosedGaussRatioCoordinateEquiv_tmul_ratio
    (s : Fin 4 ≃ Option (Fin 3)) (i : Fin 4) :
    extendedClosedGaussRatioCoordinateEquiv H I E hH e s
      (projectiveChartTransition (C := C₀) (rationalCoordinate (K := K) (n := 4))
        (s.symm none) i ⊗ₜ[C₀] (1 : E)) =
      projectiveChartTransition (C := E) zₑ (s.symm none) i := by
  change extendedClosedGaussCoefficientChartEquiv H I E hH e s
    ((1 : E) ⊗ₜ[C₀] projectiveChartTransition (C := C₀)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none) i) = _
  exact extendedClosedGaussCoefficientChartEquiv_tmul_ratio H I E hH e s i

/-- The extended field coefficients are also the actual coefficients
in the extended generic point chart. -/
theorem extendedClosedGaussRatioCoordinateEquiv_tmul_coefficient
    (s : Fin 4 ≃ Option (Fin 3)) (c : E) :
    extendedClosedGaussRatioCoordinateEquiv H I E hH e s
      ((1 : S₀ s) ⊗ₜ[C₀] c) = algebraMap E (Sₑ s) c := by
  change extendedClosedGaussCoefficientChartEquiv H I E hH e s
    (algebraMap E (E ⊗[C₀] S₀ s) c) = _
  exact (extendedClosedGaussCoefficientChartEquiv H I E hH e s).commutes c

/-- Canonical normalization after coefficient extension gives exactly
the same actual normalized extended ratio ring. -/
noncomputable def extendedClosedGaussNormalizedRatioCoordinateEquiv (s : Fin 4 ≃ Option (Fin 3)) :
    normalizationRing (S₀ s ⊗[C₀] E) ≃+* normalizationRing (Sₑ s) := by
  let b := extendedClosedGaussRatioCoordinateEquiv H I E hH e s
  let : IsDomain (S₀ s ⊗[C₀] E) := Function.Injective.isDomain b b.injective
  exact normalizationCoordinateEquiv (T := FractionRing (S₀ s ⊗[C₀] E)) b

end DimensionFourDependence
