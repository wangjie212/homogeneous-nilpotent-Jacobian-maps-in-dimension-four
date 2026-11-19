import DimensionFourDependence.ProjectivePencilContractedPrime
import DimensionFourDependence.LocalEquivCoefficientField

/-! # Horizontal Gauss parameters constructed from actual curve-prime contraction

A prime of the actual projective pencil above an original source divisor
determines a local source isomorphism. Its inverse transports the actual
Gauss coefficient field into the original source DVR. The transported
parameter has transcendental residue; no local parameter or residue
condition is part of the input.
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

omit [CharZero K] in
/-- Contracted-prime local maps preserve the original source coefficient
action and the actual Gauss coefficient action upstairs. -/
theorem projective_pencil_contracted_prime_base_scalarTowers :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    ∀ (P : Ideal G₀) [P.IsPrime] [P.LiesOver Q],
      letI : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
        Localization.AtPrime.algebraOfLiesOver Q P
      IsScalarTower K (Localization.AtPrime Q) (Localization.AtPrime P) ∧
        IsScalarTower K C₀ (Localization.AtPrime P) := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  intro P hP hlie
  let : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver Q P
  let : IsScalarTower K R₀ G₀ := IsScalarTower.of_algebraMap_eq
    (fun k => ((projectivePencilBaseInclusion H I s).commutes k).symm)
  let : IsScalarTower K R₀ (Localization.AtPrime P) := IsScalarTower.of_algebraMap_eq (by
    intro k
    rw [IsScalarTower.algebraMap_apply K G₀ (Localization.AtPrime P),
      IsScalarTower.algebraMap_apply K R₀ G₀,
      IsScalarTower.algebraMap_apply R₀ G₀ (Localization.AtPrime P)])
  let : IsScalarTower K (Localization.AtPrime Q) (Localization.AtPrime P) :=
    IsScalarTower.to₁₃₄ K R₀ (Localization.AtPrime Q) (Localization.AtPrime P)
  let : IsScalarTower K C₀ (Localization.AtPrime P) := IsScalarTower.of_algebraMap_eq (by
    intro k
    rw [IsScalarTower.algebraMap_apply K G₀ (Localization.AtPrime P),
      IsScalarTower.algebraMap_apply K C₀ G₀,
      IsScalarTower.algebraMap_apply C₀ G₀ (Localization.AtPrime P)])
  exact ⟨inferInstance, inferInstance⟩

/-- The actual closed Gauss coefficient field in the original projective
source divisor DVR, constructed solely from a prime above that divisor. -/
noncomputable def projectivePencilContractedCoefficientLift
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    ∀ (P : Ideal G₀) [P.IsPrime] [P.LiesOver Q],
      letI : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
        Localization.AtPrime.algebraOfLiesOver Q P
      {j : C₀ →ₐ[K] Localization.AtPrime Q //
        CoefficientTargetCompatible (K := K) (C := C₀)
          (A := Localization.AtPrime Q) (B := Localization.AtPrime P) j} := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  intro P hP hlie
  let : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver Q P
  obtain ⟨hKA, hKC⟩ := projective_pencil_contracted_prime_base_scalarTowers H I s Q P
  let : IsScalarTower K (Localization.AtPrime Q) (Localization.AtPrime P) := hKA
  let : IsScalarTower K C₀ (Localization.AtPrime P) := hKC
  let u := actualProjectivePencilContractedPrimeLocalEquiv H I s hH e Q f hf hQ P
  exact localEquivCoefficientLift (K := K) (C := C₀)
    (A := Localization.AtPrime Q) (B := Localization.AtPrime P) u

/-- The actual descended coefficient homomorphism, retaining its
target-compatibility proof in the underlying lift. -/
noncomputable def projectivePencilContractedCoefficientHom
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    ∀ (P : Ideal G₀) [P.IsPrime] [P.LiesOver Q], C₀ →ₐ[K] Localization.AtPrime Q := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  intro P hP hlie
  exact (projectivePencilContractedCoefficientLift H I s hH e Q f hf hQ P).val

/-- The descended coefficient map gives the same actual coefficient
under the original source-to-curve local map. -/
theorem projectivePencilContractedCoefficientHom_target
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    ∀ (P : Ideal G₀) [P.IsPrime] [P.LiesOver Q],
      letI : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
        Localization.AtPrime.algebraOfLiesOver Q P
      CoefficientTargetCompatible (K := K) (C := C₀)
        (A := Localization.AtPrime Q) (B := Localization.AtPrime P)
        (projectivePencilContractedCoefficientHom H I s hH e Q f hf hQ P) := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  intro P hP hlie
  let : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver Q P
  exact (projectivePencilContractedCoefficientLift H I s hH e Q f hf hQ P).property

/-- The actual curve-prime contraction supplies a parameter with
transcendental source-divisor residue, rather than assuming one. -/
theorem projectivePencilContractedCoefficientHom_parameter_residue_transcendental
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    ∀ (P : Ideal G₀) [P.IsPrime] [P.LiesOver Q],
      CoefficientParameterResidueTranscendental (K := K) (C := C₀)
        (A := Localization.AtPrime Q)
        (projectivePencilContractedCoefficientHom H I s hH e Q f hf hQ P) e := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  intro P hP hlie
  exact coefficientAlgHom_parameter_residue_transcendental (K := K) (C := C₀)
    (A := Localization.AtPrime Q)
    (projectivePencilContractedCoefficientHom H I s hH e Q f hf hQ P) e

end DimensionFourDependence
