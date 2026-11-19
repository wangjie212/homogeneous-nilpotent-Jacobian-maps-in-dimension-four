import DimensionFourDependence.ProjectiveHorizontalDivisor
import DimensionFourDependence.AdjoinCoordinateLocalRing
import DimensionFourDependence.SourceLocalNormalization
import DimensionFourDependence.LocalizationFunctionField

/-! # Actual projective pencil coordinate local rings at horizontal divisors

The original-coefficient projective source chart and the closed Gauss
pencil chart use the same coordinate ratios. The local coefficient-field
embedding therefore constructs the actual pencil coordinate map into the
projective source divisor local ring. Its contracted localization is the
same original projective source local ring, with every source function
preserved.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
  (I : ImageRelationWitness H) (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (s : Fin 4 ≃ Option (Fin 3))

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

/-- The actual projective pencil chart has the same local ring as the
original projective source at a horizontal divisor. The constructed
coordinate map preserves its actual source function-field realization. -/
theorem actual_projective_pencil_coordinate_source_localization
    (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
    (hX : primeLocalizationFractionHom (F := L₀) Q t =
      closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X) :
    letI : Algebra C₀ (Localization.AtPrime Q) :=
      (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
    ∃ φ : G₀ →ₐ[C₀] Localization.AtPrime Q,
      (∀ r, (primeLocalizationFractionHom (F := L₀) Q (φ r) : F₀) = r.val) ∧
      letI : Algebra G₀ (Localization.AtPrime Q) := φ.toRingHom.toAlgebra
      IsLocalization.AtPrime (Localization.AtPrime Q)
        ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).under G₀) := by
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
  let : IsFractionRing (Localization.AtPrime Q) L₀ := projective_source_divisor_isFractionRing s Q
  let : Algebra C₀ (Localization.AtPrime Q) :=
    (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
  let : IsScalarTower C₀ (Localization.AtPrime Q) L₀ :=
    closedGaussProjectiveHorizontalLocal_scalarTower H hH I e s Q t ht hX
  let : IsScalarTower R₀ (Localization.AtPrime Q) L₀ := primeLocalizationFraction_scalarTower Q
  let : Algebra (Localization.AtPrime Q) F₀ :=
    ((algebraMap L₀ F₀).comp (algebraMap (Localization.AtPrime Q) L₀)).toAlgebra
  let : IsScalarTower R₀ (Localization.AtPrime Q) F₀ := IsScalarTower.of_algebraMap_eq (by
    intro r
    change r.val = algebraMap L₀ F₀
      (algebraMap (Localization.AtPrime Q) L₀ (algebraMap R₀ (Localization.AtPrime Q) r))
    rw [← IsScalarTower.algebraMap_apply R₀ (Localization.AtPrime Q) L₀]
    rfl)
  let : IsScalarTower C₀ (Localization.AtPrime Q) F₀ := IsScalarTower.of_algebraMap_eq (by
    intro c
    change c.val = algebraMap L₀ F₀
      (algebraMap (Localization.AtPrime Q) L₀ (algebraMap C₀ (Localization.AtPrime Q) c))
    rw [← IsScalarTower.algebraMap_apply C₀ (Localization.AtPrime Q) L₀]
    rfl)
  let : FaithfulSMul (Localization.AtPrime Q) F₀ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      intro a b hab
      apply IsFractionRing.injective (Localization.AtPrime Q) L₀
      apply Subtype.val_injective
      exact hab)
  let x := fun i : Fin 4 => rationalCoordinate (K := K) i / rationalCoordinate (K := K) (s.symm none)
  let : Algebra (Algebra.adjoin K (Set.range x)) (Localization.AtPrime Q) := by
    change Algebra R₀ (Localization.AtPrime Q)
    infer_instance
  let : IsScalarTower (Algebra.adjoin K (Set.range x)) (Localization.AtPrime Q) F₀ := by
    change IsScalarTower R₀ (Localization.AtPrime Q) F₀
    infer_instance
  let : (show Ideal (Algebra.adjoin K (Set.range x)) from Q).IsPrime := by
    change Q.IsPrime
    infer_instance
  let : IsLocalization.AtPrime (Localization.AtPrime Q)
      (show Ideal (Algebra.adjoin K (Set.range x)) from Q) := by
    change IsLocalization.AtPrime (Localization.AtPrime Q) Q
    infer_instance
  let φ : G₀ →ₐ[C₀] Localization.AtPrime Q :=
    adjoinCoordinateLocalHom (K := K) (C := C₀) (A := Localization.AtPrime Q) x
  refine ⟨φ, ?_, ?_⟩
  · intro r
    exact adjoinCoordinateLocalHom_source (K := K) (A := Localization.AtPrime Q) x r
  · exact adjoin_coordinate_source_localization (K := K) (C := C₀) (A := Localization.AtPrime Q) x Q

/-- Normalizing the actual projective pencil chart recovers the original
projective source divisor DVR. The coordinate, field and normalization
maps are constructed, and all retain their actual source values. -/
theorem actual_projective_pencil_normalization_source_localization
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f})
    (t : Localization.AtPrime Q)
    (ht : Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t))
    (hX : primeLocalizationFractionHom (F := L₀) Q t =
      closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X) :
    letI : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
    letI : Algebra C₀ (Localization.AtPrime Q) :=
      (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
    ∃ (φ : G₀ →ₐ[C₀] Localization.AtPrime Q) (ψ : G₀ →ₐ[C₀] L₀),
      (∀ r, primeLocalizationFractionHom (F := L₀) Q (φ r) = ψ r) ∧
      (∀ r, (ψ r : F₀) = r.val) ∧
      letI : Algebra G₀ (Localization.AtPrime Q) := φ.toRingHom.toAlgebra
      letI : Algebra G₀ L₀ := ψ.toRingHom.toAlgebra
      IsFractionRing G₀ L₀ ∧
      ∃ η : integralClosure G₀ L₀ →ₐ[G₀] Localization.AtPrime Q,
        (∀ r, primeLocalizationFractionHom (F := L₀) Q (η r) = r.val) ∧
        letI : Algebra (integralClosure G₀ L₀) (Localization.AtPrime Q) := η.toRingHom.toAlgebra
        IsLocalization.AtPrime (Localization.AtPrime Q)
          ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).under (integralClosure G₀ L₀)) := by
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
  let : IsFractionRing (Localization.AtPrime Q) L₀ := projective_source_divisor_isFractionRing s Q
  let : Algebra C₀ (Localization.AtPrime Q) :=
    (rationalCoverHorizontalLocalHom e t ht).toRingHom.toAlgebra
  let : IsScalarTower C₀ (Localization.AtPrime Q) L₀ :=
    closedGaussProjectiveHorizontalLocal_scalarTower H hH I e s Q t ht hX
  obtain ⟨φ, hφsource, hφlocal⟩ :=
    actual_projective_pencil_coordinate_source_localization H hH I e s Q t ht hX
  let ψ : G₀ →ₐ[C₀] L₀ := (IsScalarTower.toAlgHom C₀ (Localization.AtPrime Q) L₀).comp φ
  let : Algebra G₀ (Localization.AtPrime Q) := φ.toRingHom.toAlgebra
  let : Algebra G₀ L₀ := ψ.toRingHom.toAlgebra
  let : IsScalarTower G₀ (Localization.AtPrime Q) L₀ :=
    IsScalarTower.of_algebraMap_eq (by intro r; rfl)
  let : IsDiscreteValuationRing (Localization.AtPrime Q) := projective_source_divisor_isDVR s Q f hf hQ
  let : FaithfulSMul G₀ (Localization.AtPrime Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      intro r r' hrr'
      change φ r = φ r' at hrr'
      apply Subtype.ext
      rw [← hφsource r, ← hφsource r', hrr'])
  let : IsLocalization.AtPrime (Localization.AtPrime Q)
      ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).under G₀) := hφlocal
  let : IsFractionRing G₀ L₀ := source_localization_same_fraction_field (B := Localization.AtPrime Q)
    ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).under G₀).primeCompl
  let η : integralClosure G₀ L₀ →ₐ[G₀] Localization.AtPrime Q :=
    integralClosureToNormalLocalHom (S := G₀) (A := Localization.AtPrime Q) (F := L₀)
  refine ⟨φ, ψ, ?_, ?_, inferInstance, η, ?_, ?_⟩
  · intro r
    rfl
  · intro r
    exact hφsource r
  · intro r
    exact integralClosureToNormalLocalHom_source (A := Localization.AtPrime Q) r
  · exact normalized_intermediate_algebra_source_localization (R := G₀) (S := G₀)
      ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).under G₀)

end DimensionFourDependence
