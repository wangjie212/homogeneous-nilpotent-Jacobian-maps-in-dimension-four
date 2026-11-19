import DimensionFourDependence.ProjectiveHyperplaneIntersection
import DimensionFourDependence.ProjectivePointTranscendenceLowerBound
import DimensionFourDependence.NativeProjectiveResidueIdeal
import DimensionFourDependence.NativeDivisorResidueTranscendence

/-! # Every actual normalized pencil divisor meets a hyperplane on its own branch -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory Topology
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" a:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none) ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "f" => extendedClosedGaussNormalizationProjectiveMap H I E hH e
local notation "π" => extendedClosedGaussNormalizationSchemeMap H I E hH e
local notation "j" => extendedClosedGaussPencilSchemeInclusion H I E hH e
local notation "z₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q
local notation "ha₀" a:max q:max => extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (finSuccEquiv' a) q

local instance nativeDivisorHyperplaneIntersectionIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e

/-- The actual normalization-to-source projective map is closed,
using its finite normalization and its actual closed pencil embedding. -/
theorem extendedClosedGaussNormalizationProjectiveMap_isClosedMap : IsClosedMap (f) := by
  letI : IsFinite (π) := extendedClosedGaussNormalizationSchemeMap_isFinite H I E hH e
  letI : IsClosedImmersion (j) :=
    extendedClosedGaussPencilSchemeInclusion_isClosedImmersion H I E hH e
  exact (j).isClosedEmbedding.isClosedMap.comp (π).isClosedMap

/-- Every height-one divisor of the actual normalized surface has
an original projective source image with at least linear Hilbert growth
over the same extended Gauss constants. -/
theorem actual_native_divisor_source_image_hilbert_lower_bound
    (hGauss : gaussImageDimension H I = 1)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (n : ℕ) :
    n + 1 ≤ projectiveHilbertFunction ((f) (z₀ a q)).asHomogeneousIdeal.toIdeal n := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ a q)
  obtain ⟨i, hi⟩ := actual_native_divisor_has_transcendental_original_coordinate_residue
    H I E hH e hGauss a q hq
  let x := fun k => IsLocalRing.residue ((N).presheaf.stalk (z₀ a q))
    (nativeProjectiveCoordinateGerm H I E hH e (z₀ a q) a (ha₀ a q) k)
  have hframe : x a = 1 :=
    (congrArg (IsLocalRing.residue ((N).presheaf.stalk (z₀ a q)))
      (nativeProjectiveCoordinateGerm_frame H I E hH e (z₀ a q) a (ha₀ a q))).trans (map_one _)
  have hlo := projective_point_hilbert_lower_bound_of_unit_frame_and_transcendental
    (K := E) x a i hframe hi n
  have he := native_projective_coordinate_residue_ideal_eq_image H I E hH e (z₀ a q) a (ha₀ a q)
  exact hlo.trans_eq (congrArg (fun J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E) =>
    projectiveHilbertFunction J.toIdeal n) he)

/-- A hyperplane intersection is constructed on the same actual
normalization-divisor branch. No intersection point, coefficient-field
closure, fixed curve equation or hyperplane degree calculation is supplied. -/
theorem actual_native_divisor_branch_meets_hyperplane
    (hGauss : gaussImageDimension H I = 1)
    (a : Fin 4) (q : PrimeSpectrum (normalizationRing (T₀ a))) (hq : q.asIdeal.height = 1)
    (L : MvPolynomial (Fin 4) E) (hL : L.IsHomogeneous 1) :
    ∃ z : N, (z₀ a q) ⤳ z ∧ L ∈ ((f) z).asHomogeneousIdeal := by
  exact closed_projective_branch_meets_hyperplane (f)
    (extendedClosedGaussNormalizationProjectiveMap_isClosedMap H I E hH e) (z₀ a q)
    (actual_native_divisor_source_image_hilbert_lower_bound H I E hH e hGauss a q hq) L hL

end DimensionFourDependence
