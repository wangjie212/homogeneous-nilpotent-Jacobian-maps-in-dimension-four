import DimensionFourDependence.NormalizationResidueDimensionExact
import DimensionFourDependence.TensorPencilResiduePointDimension

/-! # Exact residue and source point field dimensions at actual pencil divisors -/

namespace DimensionFourDependence

universe u

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorPencilResidueGenerationNormalizationRing
  tensorPencilResidueGenerationResidueField tensorPencilResidueGenerationCoordinateAlgebra
  tensorPencilResidueGenerationCoordinateSMul tensorPencilResidueGenerationSourceTower
  tensorPencilResidueGenerationExtendedAlgebra tensorPencilResidueGenerationClosedAlgebra
  tensorPencilResidueGenerationClosedSMul tensorPencilResidueGenerationExtendedSMul
  tensorPencilResidueGenerationClosedTower tensorPencilResidueGenerationOriginalSMul
  tensorPencilResidueGenerationOriginalTower
attribute [local instance 2000] originalTensorPencilResidueOriginalAlgebra
attribute [local instance 2000] tensorPencilResiduePointAddCommMonoid
  tensorPencilResiduePointSemiring tensorPencilResiduePointOriginalModule
  tensorPencilResiduePointOriginalMulAction

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "M₀" => projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I)
local notation "T₀" s:max => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (Equiv.symm s none) ⊗[C₀] E

/-- Each actual original tensor normalization divisor has a
one-dimensional residue fraction field over the extended coefficients. -/
theorem original_tensor_pencil_divisor_residue_relative_trdeg_eq_one
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1)
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] (hQ : Q.height = 1) :
    Algebra.trdeg E (FractionRing (normalizationRing (T₀ s) ⧸ Q)) = 1 := by
  let A := T₀ s
  let φ := originalTensorPencilCoordinateEquiv H I E s
  let : IsDomain A := original_tensor_pencil_chart_isDomain H I E s
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  let : Algebra.FiniteType C₀ (closedGaussPencilChartAlgebra H I s) :=
    closedGaussPencilChartAlgebra_finiteType H I s
  let : Algebra.FiniteType E A := (inferInstance : Algebra.FiniteType E
    (E ⊗[C₀] closedGaussPencilChartAlgebra H I s)).equiv φ.symm
  exact normalization_surface_divisor_residue_trdeg_eq_one
    (original_tensor_pencil_trdeg_two H I E hH e hGauss s) Q hQ

/-- The actual normalization divisor residue fraction field has
dimension exactly two over the original constant field. -/
theorem original_tensor_pencil_divisor_residue_trdeg_eq_two
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1)
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] (hQ : Q.height = 1) :
    Algebra.trdeg K (FractionRing (normalizationRing (T₀ s) ⧸ Q)) = 2 := by
  let L := FractionRing (normalizationRing (T₀ s) ⧸ Q)
  let : Field L := normalizationPrimeResidueFieldInstance Q
  let : Nontrivial L := (normalizationPrimeResidueFieldInstance Q).toDivisionRing.toNontrivial
  let : FaithfulSMul E L := (faithfulSMul_iff_algebraMap_injective E L).mpr (algebraMap E L).injective
  let : FaithfulSMul C₀ L := (faithfulSMul_iff_algebraMap_injective C₀ L).mpr (algebraMap C₀ L).injective
  have hrel := original_tensor_pencil_divisor_residue_relative_trdeg_eq_one H I E hH e hGauss s Q hQ
  have hCE : Algebra.trdeg C₀ E = 0 := trdeg_eq_zero
  have hCL : Algebra.trdeg C₀ L = 1 :=
    (trdeg_add_eq (A := L) C₀ E).symm.trans
      ((congrArg (fun c : Cardinal => c + Algebra.trdeg E L) hCE).trans
        ((zero_add (Algebra.trdeg E L)).trans hrel))
  calc
    Algebra.trdeg K L = Algebra.trdeg K C₀ + Algebra.trdeg C₀ L :=
      (trdeg_add_eq (A := L) K C₀).symm
    _ = 1 + 1 := congrArg₂ (· + ·) (closedGaussParameterField_trdeg_one H I hGauss) hCL
    _ = 2 := by norm_num

/-- Actual polynomial moving-plane incidence at a tensor divisor
forces its actual source point field to have dimension exactly two.
All residue field dimension and generation data are constructed. -/
theorem original_tensor_pencil_divisor_moving_plane_source_field_trdeg_eq_two
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1)
    (s : Fin 4 ≃ Option (Fin 3))
    (Q : Ideal (normalizationRing (T₀ s))) [Q.IsPrime] (hQ : Q.height = 1)
    (e₀ : RatFunc K ≃ₐ[K] M₀) (v : Fin 4 → Polynomial K)
    (hdim : Module.finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (hplane : ∑ i, (s i).elim 1 (originalTensorPencilResidueCoordinate H I E s Q) *
      Polynomial.aeval (originalTensorPencilResidueGaussParameter H I E s Q e₀) (v i) = 0) :
    Algebra.trdeg K (originalTensorPencilResiduePointField H I E s Q) = 2 :=
  (original_tensor_pencil_divisor_moving_plane_source_field_dimension H I E hH e hGauss s Q hQ
    e₀ v hdim hplane).2.1.trans
      (original_tensor_pencil_divisor_residue_trdeg_eq_two H I E hH e hGauss s Q hQ)

end DimensionFourDependence
