import DimensionFourDependence.EulerHomogeneousFractions
import DimensionFourDependence.RationalClosedGaussCover
import DimensionFourDependence.GaussRulingIncidence

/-! # The relatively closed Gauss cover has a homogeneous source parameter -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

local notation "R" => MvPolynomial (Fin 4) K
local notation "F" => FractionRing (MvPolynomial (Fin 4) K)

/-- The actual normalized normal pulled back to the rational closed cover. -/
noncomputable def closedGaussParameterNormal
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) : Fin 4 → RatFunc K :=
  fun i => e.symm ((IntermediateField.inclusion (actual_gauss_field_le_closed_parameter_field H I))
    (fullOutputCoordinate (K := K)
      (fun j => rationalImageNormal H I.equation j /
        rationalImageNormal H I.equation (imageNormalPivot H I)) i))

omit [CharZero K] in
/-- Realizing the pulled-back normal recovers the original normal ratios. -/
theorem closedGaussParameterSourceHom_normal
    (H : Fin 4 → R) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (i : Fin 4) :
    closedGaussParameterSourceHom H I e (closedGaussParameterNormal H I e i) =
      rationalImageNormal H I.equation i /
        rationalImageNormal H I.equation (imageNormalPivot H I) := by
  change (closedGaussParameterField H I).val (e (e.symm _)) = _
  rw [e.apply_symm_apply]
  rfl

/-- The actual relatively closed cover parameter is a coprime positive-degree
homogeneous quotient in the original source coordinates. -/
theorem actual_closed_gauss_parameter_reduced_homogeneous_source_quotient
    (H : Fin 4 → R) {d : ℕ} (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) :
    ∃ p q : R, ∃ D : ℕ, 0 < D ∧ p ≠ 0 ∧ q ≠ 0 ∧
      p.IsHomogeneous D ∧ q.IsHomogeneous D ∧ IsRelPrime p q ∧
      closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q := by
  apply sourceEuler_constant_reduced_homogeneous_fraction
    (closedGaussParameterSourceHom H I e RatFunc.X)
    (closedGaussParameterSourceHom_X_transcendental H I e)
  exact closedGaussParameterField_le_sourceEuler_constants H hH I (e RatFunc.X).property

/-- The finite relatively closed rational cover and its homogeneous quotient
are constructed together from the actual dimension-one Gauss image. -/
theorem exists_actual_closed_gauss_homogeneous_source_parameter
    (H : Fin 4 → R) {d : ℕ} (hH : IsHomogMap H d) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I) (p q : R) (D : ℕ),
      0 < D ∧ p ≠ 0 ∧ q ≠ 0 ∧ p.IsHomogeneous D ∧ q.IsHomogeneous D ∧
      IsRelPrime p q ∧
      closedGaussParameterSourceHom H I e RatFunc.X = algebraMap R F p / algebraMap R F q ∧
      IntermediateField.adjoin K {algebraMap R F p / algebraMap R F q} =
        closedGaussParameterField H I ∧
      algebraicClosure (closedGaussParameterField H I) F = ⊥ := by
  obtain ⟨e⟩ := actual_closed_gauss_parameter_rational_function_field H I hGauss
  obtain ⟨p, q, D, hD, hp, hq, hpH, hqH, hrel, hrep⟩ :=
    actual_closed_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  refine ⟨e, p, q, D, hD, hp, hq, hpH, hqH, hrel, hrep, ?_,
    closedGaussParameterField_relatively_closed H I⟩
  rw [← hrep]
  exact closedGaussParameterSourceHom_X_adjoin H I e

end DimensionFourDependence
