import DimensionFourDependence.FullOutputLinearCoordinates

/-! # Transporting the specified geometric constants through the output equivalence -/

namespace DimensionFourDependence

open Matrix MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] {n : ℕ}

/-- The inverse output equivalence is the restriction of the inverse
actual source-field coordinate change. -/
theorem conjugateOutputFieldEquiv_symm_source_value
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K)
    (a : polynomialOutputField (linearPolynomialConjugate T S H)) :
    ((conjugateOutputFieldEquiv T S hTS hST H).symm a : FractionRing (MvPolynomial (Fin n) K)) =
      (matrixSourceFractionEquiv T S hTS hST).symm a := by
  apply (matrixSourceFractionEquiv T S hTS hST).injective
  rw [AlgEquiv.apply_symm_apply, ← conjugateOutputFieldEquiv_source_value]
  exact congrArg (fun z : polynomialOutputField (linearPolynomialConjugate T S H) =>
    (z : FractionRing (MvPolynomial (Fin n) K)))
      ((conjugateOutputFieldEquiv T S hTS hST H).apply_symm_apply a)

/-- The same constant field, with its full-output action transported
by the specified source coordinate change. -/
noncomputable def conjugateOutputAlgebra
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E] :
    Algebra (polynomialOutputField (linearPolynomialConjugate T S H)) E :=
  ((algebraMap (polynomialOutputField H) E).comp
    (conjugateOutputFieldEquiv T S hTS hST H).symm.toRingHom).toAlgebra

/-- Transporting the output action preserves the original constant-field action. -/
theorem conjugateOutputAlgebra_isScalarTower
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E] [Algebra K E]
    [IsScalarTower K (polynomialOutputField H) E] :
    letI := conjugateOutputAlgebra T S hTS hST H E
    IsScalarTower K (polynomialOutputField (linearPolynomialConjugate T S H)) E := by
  letI := conjugateOutputAlgebra T S hTS hST H E
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap K E c = algebraMap (polynomialOutputField H) E
    ((conjugateOutputFieldEquiv T S hTS hST H).symm
      (algebraMap K (polynomialOutputField (linearPolynomialConjugate T S H)) c))
  rw [AlgEquiv.commutes]
  exact IsScalarTower.algebraMap_apply K (polynomialOutputField H) E c

/-- Algebraicity of the original geometric constants survives the
same specified output-field equivalence. -/
theorem conjugateOutputAlgebra_isAlgebraic
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin n → MvPolynomial (Fin n) K)
    (E : Type*) [Field E] [Algebra (polynomialOutputField H) E]
    [Algebra.IsAlgebraic (polynomialOutputField H) E] :
    letI := conjugateOutputAlgebra T S hTS hST H E
    Algebra.IsAlgebraic (polynomialOutputField (linearPolynomialConjugate T S H)) E := by
  letI := conjugateOutputAlgebra T S hTS hST H E
  apply (Algebra.isAlgebraic_ringHom_iff_of_comp_eq
    (conjugateOutputFieldEquiv T S hTS hST H) (RingEquiv.refl E) ?_).mpr
    (inferInstance : Algebra.IsAlgebraic (polynomialOutputField H) E)
  ext a
  change algebraMap (polynomialOutputField H) E
    ((conjugateOutputFieldEquiv T S hTS hST H).symm
      (conjugateOutputFieldEquiv T S hTS hST H a)) = algebraMap (polynomialOutputField H) E a
  rw [AlgEquiv.symm_apply_apply]

/-- The inverse source substitution on the original rational coordinates. -/
theorem matrixSourceFractionEquiv_symm_coordinate
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1)
    (i : Fin n) :
    (matrixSourceFractionEquiv T S hTS hST).symm (rationalCoordinate (K := K) i) =
      ∑ j, algebraMap K (FractionRing (MvPolynomial (Fin n) K)) (S i j) *
        rationalCoordinate (K := K) j := by
  have hinverse (p : MvPolynomial (Fin n) K) :
      (matrixSourceFractionEquiv T S hTS hST).symm (algebraMap _ _ p) =
        algebraMap _ _ (linearPolynomialPullback S p) := by
    apply (matrixSourceFractionEquiv T S hTS hST).injective
    rw [AlgEquiv.apply_symm_apply, matrixSourceFractionEquiv_polynomial,
      matrix_linear_polynomial_substitution_inverse S T hST]
  rw [rationalCoordinate, hinverse]
  simp only [linearPolynomialPullback, aeval_X, linearPolynomialMap, map_sum, map_mul,
    ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K)),
    rationalCoordinate]

end DimensionFourDependence
