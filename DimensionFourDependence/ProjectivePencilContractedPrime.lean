import DimensionFourDependence.ProjectivePencilFunctionField
import DimensionFourDependence.ProjectiveSourceDivisor
import DimensionFourDependence.BirationalPrimeLocalRing
import DimensionFourDependence.BirationalNormalizationLocalRing

/-! # Actual pencil-prime contraction recovers the projective source DVR

The source prime is an actual divisor in the original projective source
chart. Any prime of the actual pencil coordinate algebra above it has
that same source local ring. The same assertion holds for the actual
coordinate normalization. No local parameter, transcendental residue, or
preselected coefficient embedding in the source local ring is assumed.
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

include hH e in
/-- A prime of the actual projective pencil above a source divisor has
the same local ring, with its original localized source map. -/
theorem actual_projective_pencil_contracted_prime_local_map_bijective
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    ∀ (P : Ideal G₀) [P.IsPrime] [P.LiesOver Q],
      letI : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
        Localization.AtPrime.algebraOfLiesOver Q P
      Function.Bijective (algebraMap (Localization.AtPrime Q) (Localization.AtPrime P)) := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  intro P hP hlie
  let : Algebra C₀ L₀ := closedGaussProjectiveSourceAlgebra H hH I e (s.symm none)
  let : Algebra G₀ L₀ := projectivePencilSourceFieldAlgebra H I s hH e
  let : IsScalarTower R₀ G₀ L₀ := projectivePencilSourceField_scalarTower H I s hH e
  let : FaithfulSMul G₀ L₀ := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (projectivePencilSourceFieldHom_injective H I s hH e)
  let : IsDiscreteValuationRing (Localization.AtPrime Q) := projective_source_divisor_isDVR s Q f hf hQ
  exact birational_prime_source_local_map_bijective (F := L₀) Q P

/-- The actual coordinate-prime local isomorphism over the original
projective source divisor DVR, constructed from prime contraction. -/
noncomputable def actualProjectivePencilContractedPrimeLocalEquiv
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    ∀ (P : Ideal G₀) [P.IsPrime] [P.LiesOver Q],
      letI : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
        Localization.AtPrime.algebraOfLiesOver Q P
      Localization.AtPrime Q ≃ₐ[Localization.AtPrime Q] Localization.AtPrime P := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  intro P hP hlie
  let : Algebra (Localization.AtPrime Q) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver Q P
  exact AlgEquiv.ofBijective (Algebra.ofId _ _)
    (actual_projective_pencil_contracted_prime_local_map_bijective H I s hH e Q f hf hQ P)

/-- A prime of the actual projective pencil normalization above a source
divisor has the same source DVR, without an assumed horizontal parameter
or a local normalization identification. -/
theorem actual_projective_pencil_normalization_contracted_prime_local_map_bijective
    (f : R₀) (hf : Prime f) (hQ : Q = Ideal.span {f}) :
    letI : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
    letI : Algebra G₀ L₀ := projectivePencilSourceFieldAlgebra H I s hH e
    letI : IsScalarTower R₀ G₀ L₀ := projectivePencilSourceField_scalarTower H I s hH e
    BirationalNormalizationLocalMapBijective (S := G₀) (F := L₀) Q := by
  let : Algebra R₀ G₀ := (projectivePencilBaseInclusion H I s).toRingHom.toAlgebra
  let : Algebra G₀ L₀ := projectivePencilSourceFieldAlgebra H I s hH e
  let : IsScalarTower R₀ G₀ L₀ := projectivePencilSourceField_scalarTower H I s hH e
  let : IsDiscreteValuationRing (Localization.AtPrime Q) := projective_source_divisor_isDVR s Q f hf hQ
  exact birational_normalization_local_map_bijective (S := G₀) (F := L₀) Q

end DimensionFourDependence
