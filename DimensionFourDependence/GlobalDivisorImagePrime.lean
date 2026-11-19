import DimensionFourDependence.ExtendedGaussPointAtlas
import DimensionFourDependence.GlobalSourceCodimension

/-! # Dense global divisor images construct the original affine primes -/

namespace DimensionFourDependence

open AlgebraicGeometry MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual image of a generic point is the generic point of the
closure of the actual geometric image. -/
theorem scheme_generic_point_image_eq
    {X Y : Scheme.{u}} (f : Y ⟶ X) {Z : Set Y} {D : Set X}
    {y : Y} {x : X} (hy : IsGenericPoint y Z) (hx : IsGenericPoint x D)
    (himage : closure (f '' Z) = D) : f y = x := by
  have h : IsGenericPoint (f y) D := by
    simpa only [himage] using hy.image f.continuous
  exact h.eq hx

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "Pₖ" => AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K)
local notation "Nₑ" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "mₑ" => extendedClosedGaussNormalizationSourceMorphism H I E hH e

/-- Every global point over a source divisor constructs an original
tensor-normalization prime whose original source contraction has height one. -/
theorem extendedClosedGaussNormalizationPoint_source_divisor_tensor_prime
    (y : Nₑ) (hcodim : Order.coheight ((mₑ) y) = 1) :
    ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing
      (projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
        (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none)
          ⊗[closedGaussParameterField H I] E))),
      extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q = y ∧
        (extendedClosedGaussTensorNormalizationSourcePrime H I E (finSuccEquiv' a) q).asIdeal.height = 1 := by
  obtain ⟨a, q, rfl⟩ := extendedClosedGaussNormalizationPoint_exists_tensor_prime H I E hH e y
  refine ⟨a, q, rfl, ?_⟩
  have hdim : ringKrullDim ((Pₖ).presheaf.stalk ((mₑ)
      (extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q))) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hcodim]
    rfl
  have hheight := (extendedClosedGaussNormalization_source_stalk_dimension_one_iff
    H I E hH e (finSuccEquiv' a) q).mp hdim
  exact extendedClosedGaussNormalization_source_image_height_one H I E hH e (finSuccEquiv' a) q hheight

/-- Density of a prime subvariety's actual source image in a source
divisor constructs its original normalized affine prime and contraction.
No affine image equation or prime-contraction equality is assumed. -/
theorem actual_global_irreducible_source_divisor_tensor_prime
    (Z : Set Nₑ) (hZ : IsIrreducible Z) (hZclosed : IsClosed Z)
    (D₀ : Set Pₖ) (hD : IsIrreducible D₀) (hDclosed : IsClosed D₀)
    (hdiv : Order.coheight hD.genericPoint = 1)
    (himage : closure ((mₑ) '' Z) = D₀) :
    ∃ (a : Fin 4) (q : PrimeSpectrum (normalizationRing
      (projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
        (rationalCoordinate (K := K) (n := 4)) ((finSuccEquiv' a).symm none)
          ⊗[closedGaussParameterField H I] E))),
      extendedClosedGaussNormalizationTensorChartPoint H I E hH e (finSuccEquiv' a) q = hZ.genericPoint ∧
        (extendedClosedGaussTensorNormalizationSourcePrime H I E (finSuccEquiv' a) q).asIdeal.height = 1 := by
  have hpoint := scheme_generic_point_image_eq (mₑ)
    (hZ.isGenericPoint_genericPoint hZclosed) (hD.isGenericPoint_genericPoint hDclosed) himage
  apply extendedClosedGaussNormalizationPoint_source_divisor_tensor_prime H I E hH e
  rw [hpoint]
  exact hdiv

end DimensionFourDependence
