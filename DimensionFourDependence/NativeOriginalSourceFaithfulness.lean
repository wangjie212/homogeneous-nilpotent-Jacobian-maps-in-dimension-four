import DimensionFourDependence.NativeHomogeneousSourceRelations
import DimensionFourDependence.ExtendedGaussSourceMorphism

/-! # Native original projective coordinates have no original homogeneous relations -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T₀" => S₀ ⊗[C₀] E
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E

local instance nativeOriginalSourceFaithfulnessIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance nativeOriginalSourceFaithfulnessTensorDomain : IsDomain T₀ :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain
noncomputable local instance nativeOriginalSourceFaithfulnessAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- No nonzero homogeneous polynomial over the original field vanishes
at the actual native original projective source coordinates. This is
derived from the original source tensor and its injective field map. -/
theorem native_original_homogeneous_polynomial_zero_iff
    (P : MvPolynomial (Fin 4) K) {D : ℕ} (hP : P.IsHomogeneous D) :
    aeval (w) (MvPolynomial.map (ι) P) = 0 ↔ P = 0 := by
  rw [← extendedClosedGauss_source_tensor_native_homogeneous_zero_iff H I E hH e
    (MvPolynomial.map (ι) P) (hP.map _)]
  have hcoeff : MvPolynomial.map (ι) P =
      MvPolynomial.map (algebraMap C₀ E) (MvPolynomial.map (algebraMap K C₀) P) := by
    rw [MvPolynomial.map_map]
    rfl
  rw [hcoeff, extendedClosedGaussSourceTensorCoordinate_original_polynomial_value]
  constructor
  · intro he
    have hz : aeval (R := C₀) (rationalCoordinate (K := K) (n := 4))
        (MvPolynomial.map (algebraMap K C₀) P) = 0 :=
      (Algebra.TensorProduct.includeLeft : S₀ →ₐ[C₀] T₀).injective
        (he.trans (map_zero _).symm)
    rw [aeval_map_algebra_extension, rationalCoordinate_aeval] at hz
    exact (IsFractionRing.injective (MvPolynomial (Fin 4) K) S₀) (hz.trans (map_zero _).symm)
  · rintro rfl
    simp only [map_zero]

end DimensionFourDependence
