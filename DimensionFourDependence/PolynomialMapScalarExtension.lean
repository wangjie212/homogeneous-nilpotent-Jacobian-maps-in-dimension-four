import DimensionFourDependence.MatrixRankFieldMap
import DimensionFourDependence.ScalarExtendedImageEquation

/-! # Actual polynomial-map ranks under coefficient extension

The injective coefficient map extends to the actual source fraction
fields. The polynomial Jacobian commutes with this coefficient map,
and the checked field-matrix rank theorem preserves its rational rank.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The actual coefficient map from original source polynomials into
the scalar-extended source fraction field. -/
noncomputable def coefficientPolynomialToFraction :
    MvPolynomial (Fin 4) K →ₐ[K] FractionRing (MvPolynomial (Fin 4) F) :=
  (IsScalarTower.toAlgHom K (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F))).comp
    (MvPolynomial.mapAlgHom (Algebra.ofId K F))

/-- Coefficient extension into the actual extended source field is injective. -/
theorem coefficientPolynomialToFraction_injective :
    Function.Injective (coefficientPolynomialToFraction (K := K) (F := F)) :=
  (IsFractionRing.injective (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F))).comp
    (MvPolynomial.map_injective (algebraMap K F) (algebraMap K F).injective)

/-- The induced map of the actual source fraction fields. -/
noncomputable def coefficientSourceFractionMap :
    FractionRing (MvPolynomial (Fin 4) K) →ₐ[K] FractionRing (MvPolynomial (Fin 4) F) :=
  IsFractionRing.liftAlgHom (coefficientPolynomialToFraction_injective (K := K) (F := F))

/-- The fraction-field map extends the original polynomial coefficient map. -/
theorem coefficientSourceFractionMap_algebraMap (P : MvPolynomial (Fin 4) K) :
    coefficientSourceFractionMap (K := K) (F := F)
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) P) =
      algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F))
        (MvPolynomial.map (algebraMap K F) P) := by
  exact IsFractionRing.lift_algebraMap
    (coefficientPolynomialToFraction_injective (K := K) (F := F)) P

/-- The rational rank of any actual four-by-four polynomial matrix
is preserved by arbitrary coefficient-field extension. -/
theorem polyRank_map_coefficients
    (M : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) K)) :
    polyRank (M.map (MvPolynomial.map (algebraMap K F))) = polyRank M := by
  have he : (M.map (MvPolynomial.map (algebraMap K F))).map
      (algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F))) =
      (M.map (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)))).map
        (coefficientSourceFractionMap (K := K) (F := F)) := by
    ext i j
    exact (coefficientSourceFractionMap_algebraMap (F := F) (M i j)).symm
  unfold polyRank
  rw [he]
  exact matrix_rank_field_map (coefficientSourceFractionMap (K := K) (F := F)).toRingHom _

/-- The actual polynomial Jacobian commutes with coefficient extension. -/
theorem jac_map_coefficients (H : Fin 4 → MvPolynomial (Fin 4) K) :
    jac (fun i => MvPolynomial.map (algebraMap K F) (H i)) =
      (jac H).map (MvPolynomial.map (algebraMap K F)) := by
  funext i j
  exact MvPolynomial.pderiv_map (φ := algebraMap K F) (f := H i) (i := j)

/-- The actual rational Jacobian rank is unchanged after coefficient extension. -/
theorem polyRank_jac_map_coefficients (H : Fin 4 → MvPolynomial (Fin 4) K) :
    polyRank (jac (fun i => MvPolynomial.map (algebraMap K F) (H i))) = polyRank (jac H) := by
  rw [jac_map_coefficients, polyRank_map_coefficients]

end DimensionFourDependence
