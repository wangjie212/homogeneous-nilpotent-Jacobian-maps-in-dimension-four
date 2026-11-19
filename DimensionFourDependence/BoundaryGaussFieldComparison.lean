import DimensionFourDependence.ActualBoundaryGaussAlgebraicity
import DimensionFourDependence.ClosedGaussCoefficientRealization

/-! # Original Gauss-field algebraicity applies to the closed-cover parameter

The actual original Gauss field and the chosen closed-cover parameter
have compatible realizations in every actual graph coefficient field.
Their images in a boundary residue field are therefore nested. Boundary
coordinates algebraic over the original image remain algebraic over the
closed-cover parameter used in the cubic boundary equation.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] coefficientFieldScalarTower

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (I : ImageRelationWitness H) (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "M" => projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I)
local notation "f₀" => closedGaussCoefficientParameterHom H I p hY h hh e

/-- The two actual coefficient embeddings agree on every element
of the original Gauss field, before passing to boundary residues. -/
theorem original_gauss_coefficient_value_from_closed_parameter
    (m : projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    actualChartGaussFieldHom H hrank p hY I m =
      (f₀) (e.symm (algebraMap (M) (closedGaussParameterField H I) m)) := by
  apply Subtype.ext
  rw [closedGaussCoefficientParameterHom_source_value]
  change (m : S₀) = (e (e.symm (algebraMap (M) (closedGaussParameterField H I) m)) : S₀)
  rw [e.apply_symm_apply]
  rfl

variable (κ : Type u) [Field κ]
    [Algebra (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]
    [Algebra K κ]
    [IsScalarTower K (coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) κ]

/-- The actual original Gauss image in the boundary field lies in
the actual image of the closed-cover parameter used in (4.3). -/
theorem actual_boundary_original_gauss_field_le_closed_parameter_image :
    actualBoundaryOriginalGaussField H hrank p hY I κ ≤
      ((IsScalarTower.toAlgHom K (L) κ).comp (f₀)).fieldRange := by
  rintro x ⟨m, rfl⟩
  change ∃ r : RatFunc K,
    algebraMap (L) κ ((f₀) r) = algebraMap (L) κ (actualChartGaussFieldHom H hrank p hY I m)
  refine ⟨e.symm (algebraMap (M) (closedGaussParameterField H I) m), ?_⟩
  rw [← original_gauss_coefficient_value_from_closed_parameter H hrank I p hY h hh e]

/-- Coordinate algebraicity over the original Gauss image implies
the exact closed-parameter algebraicity required by the cubic equation. -/
theorem actual_boundary_original_gauss_algebraic_implies_closed_parameter_algebraic
    (v : κ) (hv : IsAlgebraic (actualBoundaryOriginalGaussField H hrank p hY I κ) v) :
    IsAlgebraic (((IsScalarTower.toAlgHom K (L) κ).comp (f₀)).fieldRange) v := by
  let J := actualBoundaryOriginalGaussField H hrank p hY I κ
  let C := ((IsScalarTower.toAlgHom K (L) κ).comp (f₀)).fieldRange
  have hle : J ≤ C := actual_boundary_original_gauss_field_le_closed_parameter_image H hrank I p hY h hh e κ
  let : Algebra J C := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  let : IsScalarTower J C κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact hv.tower_top C

end DimensionFourDependence
