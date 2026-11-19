import DimensionFourDependence.ProjectivePencilPrimeParameter
import DimensionFourDependence.CoefficientSourceCompatibility
import DimensionFourDependence.ProjectiveHorizontalDivisor

/-! # The contracted-prime parameter has its original source value

The coefficient embedding obtained from a curve-prime contraction
preserves the actual Gauss coefficients in the original projective
source field. In particular it provides a regular parameter with
transcendental residue and the original rational-parameter realization.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

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

set_option maxHeartbeats 2000000 in
/-- The coefficient descent constructed from the actual curve prime
retains every original source-field coefficient value. -/
theorem projectivePencilContractedCoefficientHom_source
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
    letI : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
    ∀ (P : Ideal G₀) [P.IsPrime] [P.LiesOver Q],
      CoefficientSourceCompatible (K := K) (C := C₀) (A := Localization.AtPrime Q) (F := L₀)
        (projectivePencilContractedCoefficientHom H I s hH e Q f hf hQ P) := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
  intro P hP hlie
  let : Algebra G₀ L₀ := projectivePencilSourceFieldAlgebra H I s hH e
  let : IsScalarTower R₀ G₀ L₀ := projectivePencilSourceField_scalarTower H I s hH e
  let : FaithfulSMul G₀ L₀ := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (projectivePencilSourceFieldHom_injective H I s hH e)
  let : Algebra (Localization.AtPrime P) L₀ := primeLocalizationFractionAlgebra P
  let : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver Q P
  let : IsScalarTower (Localization.AtPrime Q) (Localization.AtPrime P) L₀ :=
    prime_localizations_same_field_scalarTower Q P
  let : IsScalarTower G₀ (Localization.AtPrime P) L₀ := primeLocalizationFraction_scalarTower P
  let : IsScalarTower C₀ G₀ L₀ := IsScalarTower.of_algebraMap_eq
    (fun c => ((projectivePencilSourceFieldHom H I s hH e).commutes c).symm)
  let : IsScalarTower C₀ (Localization.AtPrime P) L₀ :=
    IsScalarTower.to₁₃₄ C₀ G₀ (Localization.AtPrime P) L₀
  apply coefficient_target_compatible_source (K := K) (C := C₀)
    (A := Localization.AtPrime Q) (B := Localization.AtPrime P) (F := L₀)
    (projectivePencilContractedCoefficientHom H I s hH e Q f hf hQ P)
  exact projectivePencilContractedCoefficientHom_target H I s hH e Q f hf hQ P

/-- An actual prime above the source divisor supplies all horizontal
parameter data needed by the source-DVR coefficient-extension theorem. -/
theorem actual_projective_contracted_prime_horizontal_parameter
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    ∀ (P : Ideal G₀) [P.IsPrime] [P.LiesOver Q],
      ∃ t : Localization.AtPrime Q,
        Transcendental K (IsLocalRing.residue (Localization.AtPrime Q) t) ∧
        primeLocalizationFractionHom (F := L₀) Q t =
          closedGaussProjectiveParameterSourceHom H hH I e s RatFunc.X := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  intro P hP hlie
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let : Algebra (Localization.AtPrime Q) L₀ := primeLocalizationFractionAlgebra Q
  refine ⟨projectivePencilContractedCoefficientHom H I s hH e Q f hf hQ P (e RatFunc.X),
    projectivePencilContractedCoefficientHom_parameter_residue_transcendental
      H I s hH e Q f hf hQ P, ?_⟩
  exact projectivePencilContractedCoefficientHom_source H I s hH e Q f hf hQ P (e RatFunc.X)

end DimensionFourDependence
