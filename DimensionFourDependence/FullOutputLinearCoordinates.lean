import DimensionFourDependence.FixedConeCoordinateConjugacy
import DimensionFourDependence.GenericOutputPoint

/-! # The actual full output field under invertible linear coordinates -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 2000000

variable {K F G : Type*} [Field K] [Field F] [Field G]
  [Algebra K F] [Algebra K G] {n : ℕ}

/-- Constant linear output combinations belong to the original output field. -/
theorem fullOutputField_mulVec_le (H : Fin n → F) (A : Matrix (Fin n) (Fin n) K) :
    fullOutputField (K := K) (A.map (algebraMap K F) *ᵥ H) ≤ fullOutputField (K := K) H := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  change (∑ j, algebraMap K F (A i j) * H j) ∈ fullOutputField (K := K) H
  apply (fullOutputField (K := K) H).sum_mem
  intro j _
  exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _)
    (IntermediateField.subset_adjoin K _ ⟨j, rfl⟩)

/-- An invertible target matrix preserves the entire generated field. -/
theorem fullOutputField_mulVec_eq (H : Fin n → F)
    (A B : Matrix (Fin n) (Fin n) K) (hBA : B * A = 1) :
    fullOutputField (K := K) (A.map (algebraMap K F) *ᵥ H) = fullOutputField (K := K) H := by
  have hmap : B.map (algebraMap K F) * A.map (algebraMap K F) = 1 := by
    rw [← Matrix.map_mul, hBA]
    ext i j
    simp [Matrix.one_apply]
  have hrestore : B.map (algebraMap K F) *ᵥ (A.map (algebraMap K F) *ᵥ H) = H := by
    rw [Matrix.mulVec_mulVec, hmap, Matrix.one_mulVec]
  apply le_antisymm (fullOutputField_mulVec_le H A)
  have he := fullOutputField_mulVec_le (A.map (algebraMap K F) *ᵥ H) B
  simpa only [hrestore] using he

/-- Mapping the original output field gives exactly the field of the mapped outputs. -/
theorem fullOutputField_map (f : F →ₐ[K] G) (H : Fin n → F) :
    (fullOutputField (K := K) H).map f = fullOutputField (K := K) (f ∘ H) := by
  unfold fullOutputField
  rw [IntermediateField.adjoin_map, ← Set.range_comp]

/-- The field of the conjugated polynomial map is the image of the
original output field under the actual source automorphism. -/
theorem polynomialOutputField_linearPolynomialConjugate
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K) :
    polynomialOutputField (linearPolynomialConjugate T S H) =
      (polynomialOutputField H).map (matrixSourceFractionEquiv T S hTS hST).toAlgHom := by
  let H₀ : Fin n → FractionRing (MvPolynomial (Fin n) K) := fun i => algebraMap _ _ (H i)
  have he : (fun i => algebraMap (MvPolynomial (Fin n) K)
      (FractionRing (MvPolynomial (Fin n) K)) (linearPolynomialConjugate T S H i)) =
      S.map (algebraMap K (FractionRing (MvPolynomial (Fin n) K))) *ᵥ
        ((matrixSourceFractionEquiv T S hTS hST) ∘ H₀) := by
    funext i
    exact linearPolynomialConjugate_source_value T S hTS hST H i
  change fullOutputField (K := K) _ = (fullOutputField (K := K) H₀).map _
  rw [he, fullOutputField_mulVec_eq _ S T hTS, fullOutputField_map]
  rfl

/-- The actual source automorphism restricts to the full output fields. -/
noncomputable def conjugateOutputFieldEquiv
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K) :
    polynomialOutputField H ≃ₐ[K] polynomialOutputField (linearPolynomialConjugate T S H) :=
  (IntermediateField.equivMap (polynomialOutputField H)
    (matrixSourceFractionEquiv T S hTS hST).toAlgHom).trans
      (IntermediateField.equivOfEq (polynomialOutputField_linearPolynomialConjugate T S hTS hST H).symm)

/-- This restriction agrees on every output-field element with the
original source-field coordinate change. -/
theorem conjugateOutputFieldEquiv_source_value
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K) (a : polynomialOutputField H) :
    ((conjugateOutputFieldEquiv T S hTS hST H a :
      polynomialOutputField (linearPolynomialConjugate T S H)) :
        FractionRing (MvPolynomial (Fin n) K)) = matrixSourceFractionEquiv T S hTS hST a := rfl

end DimensionFourDependence
