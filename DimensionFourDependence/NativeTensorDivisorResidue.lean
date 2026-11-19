import DimensionFourDependence.NativeNormalizationChartGermAlgebra
import DimensionFourDependence.PrimeLocalizationResidueField
import DimensionFourDependence.NormalizationResidueValue
import DimensionFourDependence.TensorPencilResidueFieldGeneration

/-! # Native divisor residues retain the original tensor quotient fraction-field coordinates -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorPencilResidueGenerationNormalizationRing
  tensorPencilResidueGenerationResidueField tensorPencilResidueGenerationCoordinateAlgebra
  tensorPencilResidueGenerationCoordinateSMul tensorPencilResidueGenerationSourceTower
  tensorPencilResidueGenerationExtendedAlgebra tensorPencilResidueGenerationExtendedSMul

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
  (a : Fin 4)

local notation "C₀" => closedGaussParameterField H I
local notation "s₀" => finSuccEquiv' a
local notation "T₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) ((s₀).symm none) ⊗[C₀] E
local notation "S₀" => normalizationRing (T₀)
local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "z₀" q:max => extendedClosedGaussNormalizationTensorChartPoint H I E hH e (s₀) q
local notation "ha₀" q:max => extendedClosedGaussNormalizationTensorChartPoint_mem_chart H I E hH e (s₀) q

local instance nativeTensorDivisorResidueIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
local instance nativeTensorDivisorResidueDomain : IsDomain (T₀) :=
  original_tensor_pencil_chart_isDomain H I E (s₀)

/-- The actual residue-field comparison together with all its
original coordinate values. Keeping the compatibility in the same
witness avoids re-expanding the concrete inverse local isomorphism. -/
noncomputable def nativeTensorDivisorResidueRealization (q : PrimeSpectrum (S₀)) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ q)
    {φ : IsLocalRing.ResidueField ((N).presheaf.stalk (z₀ q)) ≃ₐ[E]
      FractionRing ((S₀) ⧸ q.asIdeal) //
      ∀ i : Fin 3, φ (IsLocalRing.residue ((N).presheaf.stalk (z₀ q))
        (nativeProjectiveCoordinateGerm H I E hH e (z₀ q) a (ha₀ q) ((s₀).symm (some i)))) =
          originalTensorPencilResidueCoordinate H I E (s₀) q.asIdeal i} := by
  letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ q)
  let β := nativeNormalizationChartStalkAlgEquiv H I E hH e a q
  let φ := localPrimeResidueFractionAlgEquiv (E := E) q.asIdeal β
  refine ⟨φ, ?_⟩
  intro i
  let x := nativeProjectiveCoordinateGerm H I E hH e (z₀ q) a (ha₀ q) ((s₀).symm (some i))
  let r : S₀ := algebraMap (T₀) (S₀) (originalTensorPencilCoordinate H I E (s₀) i)
  have hβ : β x = algebraMap (S₀) (Localization.AtPrime q.asIdeal) r := by
    calc
      β x = β (nativeNormalizationChartGermHom H I E hH e a q r) :=
        congrArg β (nativeNormalizationChartGermHom_coordinate H I E hH e a q i).symm
      _ = _ := nativeNormalizationChartGermHom_localization H I E hH e a q r
  have he := localPrimeResidueFractionAlgEquiv_source
    (E := E) (R := S₀) (A := (N).presheaf.stalk (z₀ q)) q.asIdeal β x r hβ
  exact he.trans (normalizationPrimeResidueCoordinateAlgebra_value (A := T₀) q.asIdeal
    (originalTensorPencilCoordinate H I E (s₀) i))

/-- The actual native stalk residue field and the original tensor
normalization-prime quotient fraction field are identified over the
same extended Gauss constants. -/
noncomputable def nativeTensorDivisorResidueAlgEquiv (q : PrimeSpectrum (S₀)) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ q)
    IsLocalRing.ResidueField ((N).presheaf.stalk (z₀ q)) ≃ₐ[E]
      FractionRing ((S₀) ⧸ q.asIdeal) :=
  (nativeTensorDivisorResidueRealization H I E hH e a q).val

/-- The comparison keeps each of the original three affine source
coordinates, rather than identifying only the abstract residue fields. -/
theorem nativeTensorDivisorResidueAlgEquiv_coordinate (q : PrimeSpectrum (S₀)) (i : Fin 3) :
    letI := extendedClosedGaussStalkCoefficientAlgebra H I E hH e (z₀ q)
    nativeTensorDivisorResidueAlgEquiv H I E hH e a q
      (IsLocalRing.residue ((N).presheaf.stalk (z₀ q))
        (nativeProjectiveCoordinateGerm H I E hH e (z₀ q) a (ha₀ q) ((s₀).symm (some i)))) =
      originalTensorPencilResidueCoordinate H I E (s₀) q.asIdeal i :=
  (nativeTensorDivisorResidueRealization H I E hH e a q).property i

end DimensionFourDependence
