import DimensionFourDependence.ClosedGaussPencilCharts
import DimensionFourDependence.ReducedPointClosureScheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # The actual integral projective pencil scheme

The original source relation prime over the closed Gauss field is
homogeneous. Its generic point in the original four-coordinate projective
space defines an actual integral reduced closed subscheme. Its closed
immersion has exactly the hypersurface p - t q as its image.
-/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] [CharZero K]

local notation "R₄" => MvPolynomial (Fin 4) K
local notation "F" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" H:max I:max => closedGaussParameterField H I
local notation "𝒢" H:max I:max => homogeneousSubmodule (Fin 4) (C₀ H I)

/-- The actual homogeneous source relation prime is homogeneous over
the relatively closed Gauss parameter field. -/
theorem actual_closed_gauss_pencil_relation_ideal_isHomogeneous
    (H : Fin 4 → R₄) {d : ℕ} (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] C₀ H I) :
    (fiberVanishingIdeal (L := C₀ H I) (rationalCoordinate (K := K) (n := 4))).IsHomogeneous
      (𝒢 H I) := by
  obtain ⟨p, q, D, _, _, hq, hpH, hqH, hrel, ht⟩ :=
    actual_closed_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  rw [actual_closed_gauss_pencil_relation_ideal H I e p q hq hrel ht]
  apply Ideal.homogeneous_span
  intro P hP
  obtain rfl := Set.mem_singleton_iff.mp hP
  exact ⟨D, (actual_closed_gauss_pencil_homogeneous_degree H I e p q hq hrel hpH hqH).2.1⟩

/-- The generic point of the actual source pencil in the original
four-coordinate projective spectrum over the closed Gauss field. -/
noncomputable def closedGaussPencilProjectiveGenericPoint
    (H : Fin 4 → R₄) {d : ℕ} (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] C₀ H I) : ProjectiveSpectrum (𝒢 H I) where
  asHomogeneousIdeal :=
    { toSubmodule := fiberVanishingIdeal (L := C₀ H I) (rationalCoordinate (K := K) (n := 4))
      is_homogeneous' := actual_closed_gauss_pencil_relation_ideal_isHomogeneous H hH I e }
  isPrime := fiberVanishingIdeal_isPrime _
  not_irrelevant_le := by
    intro hle
    have hx := hle (HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < (1 : ℕ) by omega)
      (isHomogeneous_X (R := C₀ H I) (0 : Fin 4)))
    change aeval (rationalCoordinate (K := K) (n := 4)) (X (0 : Fin 4)) = 0 at hx
    rw [aeval_X] at hx
    apply (IsFractionRing.injective R₄ F).ne (X_ne_zero (0 : Fin 4))
    simpa only [rationalCoordinate, map_zero] using hx

/-- The generic point carries precisely the original source relation ideal. -/
theorem closedGaussPencilProjectiveGenericPoint_ideal
    (H : Fin 4 → R₄) {d : ℕ} (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] C₀ H I) :
    (closedGaussPencilProjectiveGenericPoint H hH I e).asHomogeneousIdeal.toIdeal =
      fiberVanishingIdeal (L := C₀ H I) (rationalCoordinate (K := K) (n := 4)) := rfl

/-- The actual global projective pencil with its reduced closed scheme structure. -/
noncomputable def closedGaussPencilScheme
    (H : Fin 4 → R₄) {d : ℕ} (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] C₀ H I) : Scheme :=
  reducedPointClosureScheme (AlgebraicGeometry.Proj (𝒢 H I))
    (closedGaussPencilProjectiveGenericPoint H hH I e)

/-- The closed pencil morphism into the original projective three-space. -/
noncomputable def closedGaussPencilSchemeInclusion
    (H : Fin 4 → R₄) {d : ℕ} (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] C₀ H I) :
    closedGaussPencilScheme H hH I e ⟶ AlgebraicGeometry.Proj (𝒢 H I) :=
  reducedPointClosureInclusion _ _

/-- The actual pencil is an integral scheme. -/
theorem closedGaussPencilScheme_isIntegral
    (H : Fin 4 → R₄) {d : ℕ} (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] C₀ H I) : IsIntegral (closedGaussPencilScheme H hH I e) :=
  reducedPointClosureScheme_isIntegral _ _

/-- The original pencil's projective inclusion is a closed immersion. -/
theorem closedGaussPencilSchemeInclusion_isClosedImmersion
    (H : Fin 4 → R₄) {d : ℕ} (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] C₀ H I) : IsClosedImmersion (closedGaussPencilSchemeInclusion H hH I e) :=
  reducedPointClosureInclusion_isClosedImmersion _ _

/-- The actual projective scheme has exactly the original reduced
homogeneous pencil hypersurface as its source image. -/
theorem closedGaussPencilSchemeInclusion_range
    (H : Fin 4 → R₄) {d : ℕ} (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] C₀ H I) (p q : R₄) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R₄ F p / algebraMap R₄ F q) :
    Set.range (closedGaussPencilSchemeInclusion H hH I e) =
      ProjectiveSpectrum.zeroLocus (𝒢 H I) {closedGaussPencilEquation H I e p q} := by
  have hc : closure {closedGaussPencilProjectiveGenericPoint H hH I e} =
      ProjectiveSpectrum.zeroLocus (𝒢 H I)
        (fiberVanishingIdeal (L := C₀ H I)
          (rationalCoordinate (K := K) (n := 4)) : Set (MvPolynomial (Fin 4) (C₀ H I))) := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    rfl
  change Set.range (reducedPointClosureInclusion _ _) = _
  rw [reducedPointClosureInclusion_range, hc,
    actual_closed_gauss_pencil_relation_ideal H I e p q hq hrel ht,
    ProjectiveSpectrum.zeroLocus_span]

end DimensionFourDependence
