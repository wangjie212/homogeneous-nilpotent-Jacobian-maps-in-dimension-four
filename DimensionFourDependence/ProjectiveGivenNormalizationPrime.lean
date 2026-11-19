import DimensionFourDependence.ProjectiveFinitePrimeModel
import DimensionFourDependence.CoefficientNormalizationPrimeContraction
import DimensionFourDependence.PrimeContractionModelTransfer

/-! # The local model starts with the given projective normalization prime

The source-divisor prime is contracted from a given prime of the actual
canonical coordinate normalization after finite coefficient extension.
Its contraction to the original pencil supplies the horizontal parameter,
so neither an auxiliary original-chart prime nor horizontal data is input.
-/

namespace DimensionFourDependence

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [CharZero K]
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

/-- The complete horizontal parameter and all finite canonical
normalization prime models, independently of how the source prime is
obtained. Keeping the statement named prevents expansion during transfer. -/
noncomputable def ProjectiveAllFiniteNormalizationPrimeModels
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) : Prop :=
  ∃ (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
    (hX : primeLocalizationFractionHom (F := L₀) Q t =
      closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X),
    ∀ (E' : Type*) [Field E'] [Algebra C₀ E'] [Module.Finite C₀ E'],
      ProjectiveFiniteNormalizationPrimeModel H I s hH e Q f hf hQ t ht hX E'

/-- The actual original pencil prime supplies the full named finite
normalization model statement before transfer to a given extended prime. -/
theorem actual_projective_original_prime_all_finite_models
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    PrimesOverSourceSatisfy (R := R₀) (T := G₀) Q
      (ProjectiveAllFiniteNormalizationPrimeModels H I s hH e Q f hf hQ) := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  exact actual_projective_contracted_prime_finite_normalization_model H I s hH e Q f hf hQ

/-- Every given prime of the actual canonical finite-coefficient pencil
normalization over an original source divisor supplies its unramified
local model. All horizontal data and original-chart primes are derived. -/
theorem actual_projective_given_normalization_prime_local_model
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f})
    (E : Type*) [Field E] [Algebra C₀ E] [Module.Finite C₀ E] :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra R₀ (G₀ ⊗[C₀] E) :=
      sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := G₀) (E := E)
    letI : Algebra R₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
      ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
        (algebraMap R₀ (G₀ ⊗[C₀] E))).toAlgebra
    PrimesOverSourceSatisfy (R := R₀) (T := normalizationRing (G₀ ⊗[C₀] E)) Q
      (ProjectiveAllFiniteNormalizationPrimeModels H I s hH e Q f hf hQ) := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra R₀ (G₀ ⊗[C₀] E) :=
    sourceCoefficientExtensionAlgebra (R := R₀) (k := C₀) (S := G₀) (E := E)
  let : Algebra R₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
    ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
      (algebraMap R₀ (G₀ ⊗[C₀] E))).toAlgebra
  let : Algebra G₀ (normalizationRing (G₀ ⊗[C₀] E)) :=
    ((algebraMap (G₀ ⊗[C₀] E) (normalizationRing (G₀ ⊗[C₀] E))).comp
      (algebraMap G₀ (G₀ ⊗[C₀] E))).toAlgebra
  refine prime_models_transfer_of_contraction (R := R₀) (S := G₀)
    (T := normalizationRing (G₀ ⊗[C₀] E)) Q
    (M := ProjectiveAllFiniteNormalizationPrimeModels H I s hH e Q f hf hQ) ?_ ?_
  · intro q hq hlie
    have hmaps :
        (algebraMap G₀ (normalizationRing (G₀ ⊗[C₀] E))).comp (algebraMap R₀ G₀) =
          algebraMap R₀ (normalizationRing (G₀ ⊗[C₀] E)) := by
      ext r
      rfl
    apply (Ideal.liesOver_iff _ _).mpr
    change Q = (q.comap (algebraMap G₀ (normalizationRing (G₀ ⊗[C₀] E)))).comap (algebraMap R₀ G₀)
    rw [Ideal.comap_comap, hmaps]
    exact Ideal.over_def q Q
  · exact actual_projective_original_prime_all_finite_models H I s hH e Q f hf hQ

end DimensionFourDependence
