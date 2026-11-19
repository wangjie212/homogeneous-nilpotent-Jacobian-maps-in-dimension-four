import DimensionFourDependence.ClosedGaussInvariantLinearForm
import DimensionFourDependence.ExtendedChosenGaussRuling

/-! # The actual graph invariant and the actual native tangent plane differ by a nonzero scalar

Both normal covectors are realized in the original source. Their source
values compare them coordinate by coordinate, including the selected
graph pivot. This comparison is independent of the rational Gauss
parameter used to construct the native ruling.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "C₀" => closedGaussParameterField H I
local notation "G₀" => projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)

/-- The original normalized image normal as a covector over the
actual closed Gauss field, retaining all four original coordinates. -/
noncomputable def actualClosedGaussNormalCovector
    (e : RatFunc K ≃ₐ[K] C₀) (i : Fin 4) : C₀ := e (closedGaussParameterNormal H I e i)

/-- The closed-field normal retains the original normalized normal
value at every original source coordinate. -/
theorem actualClosedGaussNormalCovector_source_value
    (e : RatFunc K ≃ₐ[K] C₀) (i : Fin 4) :
    (actualClosedGaussNormalCovector H I e i : S₀) =
      rationalImageNormal H I.equation i / rationalImageNormal H I.equation (imageNormalPivot H I) :=
  closedGaussParameterSourceHom_normal H I e i

/-- Every original rational parametrization of the Gauss curve has
this same actual closed-field first normal row. -/
theorem actualGaussRulingMatrix_first_row_closed_normal
    (e : RatFunc K ≃ₐ[K] C₀) (e₀ : RatFunc K ≃ₐ[K] G₀) (i : Fin 4) :
    algebraMap G₀ C₀ (actualGaussRulingMatrix H I e₀ 0 i) = actualClosedGaussNormalCovector H I e i := by
  apply Subtype.ext
  change algebraMap C₀ S₀ (algebraMap G₀ C₀ _) = _
  rw [← IsScalarTower.algebraMap_apply G₀ C₀ S₀]
  change gaussParameterSourceHom H I e₀ (gaussParameterNormal H I e₀ i) =
    (actualClosedGaussNormalCovector H I e i : S₀)
  rw [gaussParameterSourceHom_normal, actualClosedGaussNormalCovector_source_value]

variable (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))

local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "ν" => actualClosedGaussFirstInvariantCovector H I p hY h hh

include hY hh

/-- The actual normal's graph pivot is a nonzero closed Gauss
coefficient, so it can rescale the actual root forms. -/
theorem actualClosedGaussNormalCovector_graph_pivot_ne_zero
    (e : RatFunc K ≃ₐ[K] C₀) : actualClosedGaussNormalCovector H I e (p 3) ≠ 0 := by
  obtain ⟨hlast, _⟩ := I.gauss_chart_ratios H p hY h hh
  intro hz
  have he := congrArg (fun z : C₀ => (z : S₀)) hz
  rw [actualClosedGaussNormalCovector_source_value] at he
  exact (div_ne_zero hlast (imageNormalPivot_ne_zero H I)) he

/-- The actual first-invariant covector is exactly the actual image
normal divided by its graph pivot. All coefficients lie in the same
actual closed Gauss field. -/
theorem actualClosedGaussNormalCovector_eq_graph_pivot_mul
    (e : RatFunc K ≃ₐ[K] C₀) (i : Fin 4) :
    actualClosedGaussNormalCovector H I e i =
      actualClosedGaussNormalCovector H I e (p 3) * (ν) i := by
  obtain ⟨hlast, hcoord⟩ := I.gauss_chart_ratios H p hY h hh
  obtain ⟨j, rfl⟩ := p.surjective i
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [actualClosedGaussFirstInvariantCovector, Function.comp_apply,
      Equiv.symm_apply_apply, Fin.snoc_last, mul_one]
    rfl
  · apply Subtype.ext
    simp only [IntermediateField.coe_mul, actualClosedGaussNormalCovector_source_value,
      actualClosedGaussFirstInvariantCovector, Function.comp_apply, Equiv.symm_apply_apply,
      Fin.snoc_castSucc, IntermediateField.coe_neg]
    change rationalImageNormal H I.equation (p j.castSucc) /
        rationalImageNormal H I.equation (imageNormalPivot H I) =
      (rationalImageNormal H I.equation (p 3) /
        rationalImageNormal H I.equation (imageNormalPivot H I)) *
          -(coefficientPartial (Y) hY j h : S₀)
    have hpart := hcoord j
    change rationalImageNormal H I.equation (p j.castSucc) /
      rationalImageNormal H I.equation (p 3) = -(coefficientPartial (Y) hY j h : S₀) at hpart
    rw [(div_eq_iff hlast).mp hpart]
    ring

end DimensionFourDependence
