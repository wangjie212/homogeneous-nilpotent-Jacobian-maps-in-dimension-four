import DimensionFourDependence.LinearSubst
import DimensionFourDependence.MatrixRankFieldMap

/-! # Linear polynomial coordinates for restrictions to a vector subspace

Matrix substitution evaluates as the corresponding linear map, preserves
homogeneity, and has exactly the original matrix as its constant Jacobian.
These facts support plane restrictions and the exclusion of contained planes.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {F : Type*} [Field F] {m n : ℕ}

/-- The polynomial coordinate map associated to a matrix. -/
noncomputable def linearPolynomialMap (A : Matrix (Fin m) (Fin n) F) :
    Fin m → MvPolynomial (Fin n) F := fun i => ∑ j, C (A i j) * X j

/-- Evaluation of a linear coordinate map is matrix-vector multiplication. -/
theorem linearPolynomialMap_aeval (A : Matrix (Fin m) (Fin n) F) (x : Fin n → F) :
    (fun i => aeval x (linearPolynomialMap A i)) = A *ᵥ x := by
  funext i
  simp [linearPolynomialMap, Matrix.mulVec, dotProduct]

/-- Every coordinate form is homogeneous of degree one. -/
theorem linearPolynomialMap_homogeneous (A : Matrix (Fin m) (Fin n) F) (i : Fin m) :
    (linearPolynomialMap A i).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  exact isHomogeneous_C_mul_X (A i j) j

/-- Restriction of a polynomial along a matrix-defined linear map. -/
noncomputable def linearPolynomialPullback (A : Matrix (Fin m) (Fin n) F)
    (R : MvPolynomial (Fin m) F) : MvPolynomial (Fin n) F := aeval (linearPolynomialMap A) R

/-- The restriction has the correct pointwise evaluation. -/
theorem linearPolynomialPullback_aeval (A : Matrix (Fin m) (Fin n) F)
    (R : MvPolynomial (Fin m) F) (x : Fin n → F) :
    aeval x (linearPolynomialPullback A R) = aeval (A *ᵥ x) R := by
  unfold linearPolynomialPullback
  rw [comp_aeval_apply, linearPolynomialMap_aeval]

/-- Linear restriction preserves the actual homogeneous degree. -/
theorem linearPolynomialPullback_homogeneous (A : Matrix (Fin m) (Fin n) F)
    (R : MvPolynomial (Fin m) F) {d : ℕ} (hR : R.IsHomogeneous d) :
    (linearPolynomialPullback A R).IsHomogeneous d := by
  simpa only [linearPolynomialPullback, one_mul] using
    hR.aeval (linearPolynomialMap A) (linearPolynomialMap_homogeneous A)

/-- Evaluation in coordinates of an arbitrary finite-dimensional linear map. -/
theorem linearPolynomialPullback_toMatrix_aeval
    (f : (Fin n → F) →ₗ[F] (Fin m → F)) (R : MvPolynomial (Fin m) F) (x : Fin n → F) :
    aeval x (linearPolynomialPullback (LinearMap.toMatrix' f) R) = aeval (f x) R := by
  rw [linearPolynomialPullback_aeval]
  change aeval ((Matrix.toLin' (LinearMap.toMatrix' f)) x) R = _
  rw [Matrix.toLin'_toMatrix']

/-- The Jacobian of a square linear polynomial map is its constant coefficient matrix. -/
theorem jac_linearPolynomialMap (A : Matrix (Fin n) (Fin n) F) :
    jac (linearPolynomialMap A) = A.map MvPolynomial.C := by
  ext i j
  simp [jac, linearPolynomialMap, Derivation.leibniz, pderiv_X, Pi.single_apply]

/-- Its polynomial Jacobian rank is the rank of the original matrix. -/
theorem polyRank_jac_linearPolynomialMap (A : Matrix (Fin n) (Fin n) F) :
    polyRank (jac (linearPolynomialMap A)) = A.rank := by
  rw [jac_linearPolynomialMap]
  unfold polyRank
  have he : (A.map MvPolynomial.C).map
      (algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))) =
      A.map (algebraMap F (FractionRing (MvPolynomial (Fin n) F))) := by
    ext i j
    rfl
  rw [he, matrix_rank_field_map]

end DimensionFourDependence
