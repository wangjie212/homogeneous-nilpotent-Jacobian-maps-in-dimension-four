import DimensionFourDependence.ProjectivePencilPrimeSource
import DimensionFourDependence.ProjectivePencilLocalRing
import DimensionFourDependence.IntermediateDenominatorLocalization

/-! # The actual projective pencil source denominator model

The constructed coordinate homomorphism in the source DVR preserves the
original source functions. Consequently inverting the original source
prime-complement denominators gives that DVR, before coefficient extension.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (s : Fin 4 ≃ Option (Fin 3)) {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "F₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "R₀" => projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "G₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)
local notation "L₀" => projectiveCoordinateChartField (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none)

variable (Q : Ideal (projectiveCoordinateChartAlgebra (C := K)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none))) [Q.IsPrime]

/-- The full actual source-denominator model, including its map and the
coefficient, original-source, and denominator actions. -/
noncomputable def ProjectivePencilSourceDenominatorModel
    (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t)) : Prop :=
  letI : Algebra C₀ (Localization.AtPrime Q) :=
    (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
  ∃ φ : G₀ →ₐ[C₀] Localization.AtPrime Q,
    (∀ r, (primeLocalizationFractionHom (F := L₀) Q (φ r) : F₀) = r.val) ∧
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra G₀ (Localization.AtPrime Q) := φ.toRingHom.toAlgebra
    IsScalarTower R₀ G₀ (Localization.AtPrime Q) ∧
    FaithfulSMul G₀ (Localization.AtPrime Q) ∧
    IsLocalization (Algebra.algebraMapSubmonoid G₀ Q.primeCompl) (Localization.AtPrime Q)

/-- The actual horizontal projective pencil chart becomes the source
DVR after inverting exactly the original source divisor denominators. -/
theorem actual_projective_pencil_source_denominator_model
    (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
    (hX : primeLocalizationFractionHom (F := L₀) Q t =
      closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X) :
    ProjectivePencilSourceDenominatorModel H I s e Q t ht := by
  let : Algebra C₀ (Localization.AtPrime Q) :=
    (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
  obtain ⟨φ, hφ, _⟩ := actual_projective_pencil_coordinate_source_localization H hH I e s Q t ht hX
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra G₀ (Localization.AtPrime Q) := φ.toRingHom.toAlgebra
  let : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
  let : IsFractionRing (Localization.AtPrime Q) L₀ := projective_source_divisor_isFractionRing s Q
  let : IsScalarTower R₀ G₀ (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (by
    intro r
    apply IsFractionRing.injective (Localization.AtPrime Q) L₀
    apply Subtype.val_injective
    change (primeLocalizationFractionHom (F := L₀) Q (algebraMap R₀ (Localization.AtPrime Q) r) : F₀) =
      (primeLocalizationFractionHom (F := L₀) Q (φ (projectivePencilBaseInclusion H I s r)) : F₀)
    rw [primeLocalizationFractionHom_algebraMap, hφ]
    rfl)
  let : FaithfulSMul G₀ (Localization.AtPrime Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      intro r r' hrr'
      apply Subtype.ext
      rw [← hφ r, ← hφ r']
      exact congrArg (fun a => (primeLocalizationFractionHom (F := L₀) Q a : F₀)) hrr')
  exact ⟨φ, hφ, inferInstance, inferInstance,
    intermediate_algebra_denominator_localization (R := R₀) (S := G₀)
      (A := Localization.AtPrime Q) Q.primeCompl⟩

end DimensionFourDependence
