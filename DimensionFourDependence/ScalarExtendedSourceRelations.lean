import DimensionFourDependence.ExtendedGaussPencilPrime
import DimensionFourDependence.RelativelyClosedAlgebraicBaseChange
import DimensionFourDependence.FiberAlgebraicBaseChange
import DimensionFourDependence.ProjectiveLineAtlasPoints

/-! # Actual coefficient-extended source evaluation has the extended pencil kernel

The actual source tensor is a field. Its polynomial evaluation prime
contracts to the original source prime. Algebraic coefficient extension
is integral, and the extended original pencil ideal is already prime;
incomparability therefore identifies these exact relation ideals.
-/

namespace DimensionFourDependence

open MvPolynomial
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.algebraMvPolynomial

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "T" => S₀ ⊗[C₀] E
local notation "x₀" => rationalCoordinate (K := K) (n := 4)

local instance scalarExtendedSourceRelationsRightTower : IsScalarTower C₀ E T :=
  IsScalarTower.of_algebraMap_eq
    (fun c => (Algebra.TensorProduct.includeRight.commutes c).symm)

local instance scalarExtendedSourceRelationsDomain : IsDomain T :=
  (actual_closed_gauss_cover_algebraic_base_change_isField H I E).isDomain

/-- The original four source coordinates inside their actual
coefficient-extended source tensor field. -/
noncomputable def extendedClosedGaussSourceTensorCoordinate (i : Fin 4) : T := (x₀) i ⊗ₜ[C₀] (1 : E)

/-- Original source-polynomial values retain their exact original
value in the left factor of the actual source tensor. -/
theorem extendedClosedGaussSourceTensorCoordinate_original_polynomial_value
    (P : MvPolynomial (Fin 4) C₀) :
    aeval (extendedClosedGaussSourceTensorCoordinate H I E) (MvPolynomial.map (algebraMap C₀ E) P) =
      (Algebra.TensorProduct.includeLeft : S₀ →ₐ[C₀] T) (aeval (x₀) P) := by
  rw [aeval_map_algebra_extension]
  exact (comp_aeval_apply (x₀) (Algebra.TensorProduct.includeLeft : S₀ →ₐ[C₀] T) P).symm

/-- Polynomial evaluation in the actual coefficient-extended source
field has exactly the extended original pencil relation ideal. -/
theorem extendedClosedGaussSourceTensorCoordinate_relations :
    RingHom.ker (aeval (R := E) (extendedClosedGaussSourceTensorCoordinate H I E)).toRingHom =
      extendedClosedGaussPencilIdeal H I E := by
  let J := RingHom.ker (aeval (R := E) (extendedClosedGaussSourceTensorCoordinate H I E)).toRingHom
  let : J.IsPrime := RingHom.ker_isPrime _
  have hcomp : J.comap (MvPolynomial.map (algebraMap C₀ E)) = fiberVanishingIdeal (L := C₀) (x₀) := by
    ext P
    change aeval (extendedClosedGaussSourceTensorCoordinate H I E) (MvPolynomial.map (algebraMap C₀ E) P) = 0 ↔
      aeval (x₀) P = 0
    rw [extendedClosedGaussSourceTensorCoordinate_original_polynomial_value]
    exact map_eq_zero_iff _ (Algebra.TensorProduct.includeLeft : S₀ →ₐ[C₀] T).injective
  have hint : (MvPolynomial.map (algebraMap C₀ E) (σ := Fin 4)).IsIntegral := by
    rw [← MvPolynomial.algebraMap_def]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  have hmin := prime_minimal_over_integral_extension (MvPolynomial.map (algebraMap C₀ E)) hint
    (fiberVanishingIdeal (L := C₀) (x₀)) J hcomp
  exact le_antisymm (hmin.2 ⟨extendedClosedGaussPencilIdeal_isPrime H I E, le_rfl⟩ hmin.le) hmin.le

/-- Exact membership in the extended pencil ideal is equivalent to
vanishing at the original coordinates in the actual source tensor field. -/
theorem extendedClosedGaussSourceTensorCoordinate_zero_iff
    (P : MvPolynomial (Fin 4) E) :
    aeval (extendedClosedGaussSourceTensorCoordinate H I E) P = 0 ↔ P ∈ extendedClosedGaussPencilIdeal H I E := by
  change P ∈ RingHom.ker (aeval (R := E) (extendedClosedGaussSourceTensorCoordinate H I E)).toRingHom ↔ _
  rw [extendedClosedGaussSourceTensorCoordinate_relations]

end DimensionFourDependence
