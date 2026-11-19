import DimensionFourDependence.TensorPencilResidueFieldGeneration
import DimensionFourDependence.NormalizationResidueDimension

/-! # Actual pencil normalization divisors have total dimension at least two -/

namespace DimensionFourDependence

universe u

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorPencilResidueGenerationNormalizationRing
  tensorPencilResidueGenerationResidueField tensorPencilResidueGenerationCoordinateAlgebra
  tensorPencilResidueGenerationCoordinateSMul tensorPencilResidueGenerationSourceTower
  tensorPencilResidueGenerationExtendedAlgebra
  tensorPencilResidueGenerationClosedAlgebra tensorPencilResidueGenerationClosedSMul
  tensorPencilResidueGenerationExtendedSMul tensorPencilResidueGenerationClosedTower
  tensorPencilResidueGenerationOriginalSMul tensorPencilResidueGenerationOriginalTower
attribute [local instance 2000] originalTensorPencilResidueOriginalAlgebra

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "T₀" s:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm s none) ⊗[C₀] E

/-- Every height-one prime of the actual original tensor-pencil
normalization has residue fraction field of transcendence degree at least
two over the original constants. The surface dimension, finite
normalization, nonclosedness and Gauss-parameter contribution are derived. -/
theorem original_tensor_pencil_divisor_residue_trdeg_at_least_two
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1)
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] (hQ : Q.height = 1) :
    2 ≤ Algebra.trdeg K (FractionRing (normalizationRing (T₀ s) ⧸ Q)) := by
  let A := T₀ s
  let L := FractionRing (normalizationRing A ⧸ Q)
  let : Field L := normalizationPrimeResidueFieldInstance Q
  let : Nontrivial L := (normalizationPrimeResidueFieldInstance Q).toDivisionRing.toNontrivial
  let : FaithfulSMul E L := (faithfulSMul_iff_algebraMap_injective E L).mpr
    (algebraMap E L).injective
  let : FaithfulSMul C₀ L := (faithfulSMul_iff_algebraMap_injective C₀ L).mpr
    (algebraMap C₀ L).injective
  let φ := originalTensorPencilCoordinateEquiv H I E s
  let : IsDomain A := original_tensor_pencil_chart_isDomain H I E s
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  let : Algebra.FiniteType C₀ (closedGaussPencilChartAlgebra H I s) :=
    closedGaussPencilChartAlgebra_finiteType H I s
  let : Algebra.FiniteType E A := (inferInstance : Algebra.FiniteType E
    (E ⊗[C₀] closedGaussPencilChartAlgebra H I s)).equiv φ.symm
  have hsurface : 2 ≤ Algebra.trdeg E A :=
    (original_tensor_pencil_trdeg_two H I E hH e hGauss s).ge
  have hrel : 1 ≤ Algebra.trdeg E L := normalization_divisor_residue_trdeg_at_least_one
    hsurface Q hQ
  have hCE : Algebra.trdeg C₀ E = 0 := trdeg_eq_zero
  have hCL : Algebra.trdeg E L = Algebra.trdeg C₀ L :=
    (zero_add (Algebra.trdeg E L)).symm.trans
      ((congrArg (fun c : Cardinal => c + Algebra.trdeg E L) hCE.symm).trans
        (trdeg_add_eq (A := L) C₀ E))
  have hbase : 1 ≤ Algebra.trdeg K C₀ := (closedGaussParameterField_trdeg_one H I hGauss).ge
  calc
    2 = (1 : Cardinal) + 1 := by norm_num
    _ ≤ Algebra.trdeg K C₀ + Algebra.trdeg C₀ L := add_le_add hbase (hrel.trans_eq hCL)
    _ = Algebra.trdeg K L := trdeg_add_eq (A := L) K C₀

end DimensionFourDependence
