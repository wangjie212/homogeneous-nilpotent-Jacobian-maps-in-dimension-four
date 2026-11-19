import DimensionFourDependence.NormalizationResidueCoordinateField
import DimensionFourDependence.ClosedGaussCoefficientImages
import DimensionFourDependence.TensorPencilProjectionFieldActions

/-! # Original source coordinates and the actual Gauss parameter generate residue fields -/

namespace DimensionFourDependence

universe u

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option quotPrecheck false

variable {K : Type u} [Field K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  (s : Fin 4 ≃ Option (Fin 3))

local notation "C₀" => closedGaussParameterField H I
local notation "M₀" => projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I)
local notation "T₀" => projectiveCoordinateChartAlgebra (C := C₀)
  (rationalCoordinate (K := K) (n := 4)) (s.symm none) ⊗[C₀] E

noncomputable local instance tensorPencilResidueGenerationNormalizationRing :
    CommRing (normalizationRing T₀) := normalizationRingCommRingInstance

variable (Q : Ideal (normalizationRing
  (projectiveCoordinateChartAlgebra (C := closedGaussParameterField H I)
    (rationalCoordinate (K := K) (n := 4)) (s.symm none) ⊗[closedGaussParameterField H I] E)))
  [Q.IsPrime]

local notation "L₀" => FractionRing (normalizationRing T₀ ⧸ Q)

noncomputable local instance tensorPencilResidueGenerationResidueField : Field L₀ :=
  normalizationPrimeResidueFieldInstance Q
noncomputable local instance tensorPencilResidueGenerationCoordinateAlgebra : Algebra T₀ L₀ :=
  normalizationPrimeResidueCoordinateAlgebra Q
noncomputable local instance tensorPencilResidueGenerationCoordinateSMul : SMul T₀ L₀ :=
  (normalizationPrimeResidueCoordinateAlgebra Q).toSMul
noncomputable local instance tensorPencilResidueGenerationExtendedAlgebra : Algebra E L₀ :=
  normalizationPrimeResidueCoefficientAlgebra Q
noncomputable local instance tensorPencilResidueGenerationClosedAlgebra : Algebra C₀ L₀ :=
  normalizationPrimeResidueCoefficientAlgebra Q
noncomputable local instance tensorPencilResidueGenerationClosedSMul : SMul C₀ L₀ :=
  (normalizationPrimeResidueCoefficientAlgebra (E := C₀) Q).toSMul
noncomputable local instance tensorPencilResidueGenerationExtendedSMul : SMul E L₀ :=
  (normalizationPrimeResidueCoefficientAlgebra (E := E) Q).toSMul
local instance tensorPencilResidueGenerationClosedTower : IsScalarTower C₀ E L₀ :=
  normalizationPrimeResidueCoefficientAlgebra_coefficient_tower Q
local instance tensorPencilResidueGenerationSourceTower : IsScalarTower E T₀ L₀ :=
  normalizationPrimeResidueCoefficientAlgebra_source_tower Q

/-- The original coefficient action on the actual normalization prime
residue fraction field, through the actual closed Gauss coefficient field. -/
@[instance_reducible]
noncomputable def originalTensorPencilResidueOriginalAlgebra : Algebra K L₀ :=
  ((algebraMap C₀ L₀).comp (algebraMap K C₀)).toAlgebra

attribute [local instance 2000] originalTensorPencilResidueOriginalAlgebra

noncomputable local instance tensorPencilResidueGenerationOriginalSMul : SMul K L₀ :=
  (originalTensorPencilResidueOriginalAlgebra H I E s Q).toSMul
local instance tensorPencilResidueGenerationOriginalTower : IsScalarTower K C₀ L₀ :=
  IsScalarTower.of_algebraMap_eq (R := K) (S := C₀) (A := L₀) (fun _ => rfl)

/-- The original three affine coordinate values at the actual
normalization prime, in its canonical quotient fraction field. -/
noncomputable def originalTensorPencilResidueCoordinate (i : Fin 3) : L₀ :=
  algebraMap T₀ L₀ (originalTensorPencilCoordinate H I E s i)

/-- The actual Gauss parameter retains its prescribed value after
coefficient extension, normalization and passage to the prime residue field. -/
noncomputable def originalTensorPencilResidueGaussParameter
    (e₀ : RatFunc K ≃ₐ[K] M₀) : L₀ :=
  algebraMap C₀ L₀ (algebraMap M₀ C₀ (e₀ RatFunc.X))

/-- The field of the source point is generated over the original
coefficient field by the actual three original coordinate residues. -/
noncomputable def originalTensorPencilResiduePointField : IntermediateField K L₀ :=
  IntermediateField.adjoin K (Set.range (originalTensorPencilResidueCoordinate H I E s Q))

/-- For every actual tensor normalization prime, a field containing
its original coordinate residues and actual Gauss parameter makes the
whole residue fraction field algebraic. No generation hypothesis on that
residue field is supplied. -/
theorem original_tensor_pencil_residue_isAlgebraic_of_coordinates_and_parameter
    (e₀ : RatFunc K ≃ₐ[K] M₀) (J : IntermediateField K L₀)
    (ht : originalTensorPencilResidueGaussParameter H I E s Q e₀ ∈ J)
    (hx : ∀ i, originalTensorPencilResidueCoordinate H I E s Q i ∈ J) :
    Algebra.IsAlgebraic J L₀ := by
  let : Field J := IntermediateField.toField J
  let : Nontrivial J := (IntermediateField.toField J).toDivisionRing.toNontrivial
  apply normalization_prime_residue_fraction_field_isAlgebraic Q
    (originalTensorPencilCoordinate H I E s) (originalTensorPencilCoordinate_adjoin H I E s)
  · exact closed_gauss_extended_coefficient_images_isAlgebraic H I (E := E) (L := L₀) e₀ J ht
  · intro i
    exact isAlgebraic_algebraMap
      (⟨originalTensorPencilResidueCoordinate H I E s Q i, hx i⟩ : J)

/-- The actual normalization-prime residue field is algebraic over
the source point field with the actual Gauss parameter adjoined. This is
the field-generation input to the moving-plane dimension argument. -/
theorem original_tensor_pencil_residue_isAlgebraic_over_point_and_parameter
    (e₀ : RatFunc K ≃ₐ[K] M₀) :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin (originalTensorPencilResiduePointField H I E s Q)
        {originalTensorPencilResidueGaussParameter H I E s Q e₀}) L₀ := by
  let F := originalTensorPencilResiduePointField H I E s Q
  let t := originalTensorPencilResidueGaussParameter H I E s Q e₀
  let J := IntermediateField.adjoin F {t}
  have ht : t ∈ J := IntermediateField.subset_adjoin F {t} (Set.mem_singleton t)
  have hx (i : Fin 3) : originalTensorPencilResidueCoordinate H I E s Q i ∈ J := by
    have hi : originalTensorPencilResidueCoordinate H I E s Q i ∈ F :=
      IntermediateField.subset_adjoin K _ (Set.mem_range_self i)
    exact J.algebraMap_mem ⟨_, hi⟩
  exact original_tensor_pencil_residue_isAlgebraic_of_coordinates_and_parameter H I E s Q e₀
    (J.restrictScalars K) ht hx

end DimensionFourDependence
