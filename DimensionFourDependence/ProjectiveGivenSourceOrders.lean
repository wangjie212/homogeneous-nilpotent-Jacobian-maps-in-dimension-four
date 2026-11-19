import DimensionFourDependence.ProjectiveGivenNormalizationPrime
import DimensionFourDependence.ProjectiveFiniteSourceOrders
import DimensionFourDependence.LocalEquivSourceFieldCompatibility

/-! # Source-order comparison from the given projective normalization prime

The actual given normalization prime supplies the horizontal parameter.
All original-source maps and regular and rational order comparisons on
every finite-coefficient canonical normalization are then constructed.
No auxiliary pencil prime or local order comparison is an assumption.
-/

namespace DimensionFourDependence

universe u v w

section Transfer

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]

/-- Transfer a proved conclusion for every given prime without changing
the prime, source action, or contraction condition. -/
theorem primesOverSourceSatisfy_imp (Q : Ideal R) {M M' : Prop}
    (h : PrimesOverSourceSatisfy (T := T) Q M) (himp : M → M') :
    PrimesOverSourceSatisfy (T := T) Q M' := by
  intro q hq hlie
  exact himp (@h q hq hlie)

end Transfer

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (s : Fin 4 ≃ Option (Fin 3)) {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "G₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "L₀" => projectiveCoordinateChartField (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)

variable (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]

/-- The constructed horizontal parameter and every finite canonical
normalization's actual regular and rational source-order comparisons. -/
noncomputable def ProjectiveAllFiniteNormalizationSourceOrders
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) : Prop :=
  ∃ (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
    (hX : primeLocalizationFractionHom (F := L₀) Q t =
      closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X),
    ∀ (E' : Type w) [Field E'] [Algebra C₀ E'] [Module.Finite C₀ E'],
      ProjectiveFiniteNormalizationSourceOrders H I s hH e Q f hf hQ t ht hX E'

/-- The parameter data constructed by the actual given-prime local
model supplies the full regular and rational source-order conclusion. -/
theorem projective_all_finite_prime_models_source_orders
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f})
    (h : ProjectiveAllFiniteNormalizationPrimeModels.{u, w} H I s hH e Q f hf hQ) :
    ProjectiveAllFiniteNormalizationSourceOrders.{u, w} H I s hH e Q f hf hQ := by
  obtain ⟨t, ht, hX, _⟩ := h
  refine ⟨t, ht, hX, ?_⟩
  intro E hE halg hfinite
  exact actual_projective_finite_normalization_source_orders H I s hH e Q f hf hQ t ht hX E

/-- A given prime of the actual canonical projective normalization over
the source divisor constructs all horizontal data and the exact regular
and rational source-order comparisons in its actual local ring. -/
theorem actual_projective_given_normalization_prime_source_orders
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f})
    (E : Type v) [Field E] [Algebra C₀ E] [Module.Finite C₀ E] :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra R₀ (G₀ ⊗[C₀] E) :=
      sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := G₀) (E := E)
    letI : Algebra R₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
      ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
        (algebraMap R₀ (G₀ ⊗[C₀] E))).toAlgebra
    PrimesOverSourceSatisfy (R := R₀) (T := normalizationRing (G₀ ⊗[C₀] E)) Q
      (ProjectiveAllFiniteNormalizationSourceOrders.{u, w} H I s hH e Q f hf hQ) := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ (G₀ ⊗[C₀] E) :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := G₀) (E := E)
  let : Algebra R₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
    ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
      (algebraMap R₀ (G₀ ⊗[C₀] E))).toAlgebra
  refine primesOverSourceSatisfy_imp (R := R₀) (T := normalizationRing (G₀ ⊗[C₀] E)) Q
    (M := ProjectiveAllFiniteNormalizationPrimeModels.{u, w} H I s hH e Q f hf hQ)
    (M' := ProjectiveAllFiniteNormalizationSourceOrders.{u, w} H I s hH e Q f hf hQ) ?_ ?_
  · exact actual_projective_given_normalization_prime_local_model.{u, v, w} H I s hH e Q f hf hQ E
  · exact projective_all_finite_prime_models_source_orders.{u, w} H I s hH e Q f hf hQ

end DimensionFourDependence
