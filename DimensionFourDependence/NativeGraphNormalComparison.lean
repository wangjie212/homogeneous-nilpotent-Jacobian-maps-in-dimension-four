import DimensionFourDependence.ClosedGaussNormalComparison

/-! # The constructed graph linear form and chosen native tangent-plane section agree up to a unit

The first row of every actual Gauss ruling is the same normalized image
normal. Its nonzero graph pivot gives the precise scalar relating the
constructed first-invariant linear form and the chosen native plane.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix AlgebraicGeometry

attribute [local instance] coefficientFieldScalarTower

universe u

set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3)))
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "C₀" => closedGaussParameterField H I
local notation "G₀" => projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I)
local notation "ν" => actualClosedGaussFirstInvariantCovector H I p hY h hh
local notation "λ" => algebraMap C₀ E (actualClosedGaussNormalCovector H I e (p 3))

/-- The extended ruling's first normal row is the exact original
closed-field normal, independent of the rational Gauss parametrization. -/
theorem extendedClosedGaussRulingMatrix_first_row_closed_normal
    (e₀ : RatFunc K ≃ₐ[K] G₀) (i : Fin 4) :
    extendedClosedGaussRulingMatrix H I E e₀ 0 i =
      algebraMap C₀ E (actualClosedGaussNormalCovector H I e i) := by
  change algebraMap C₀ E (algebraMap G₀ C₀ (actualGaussRulingMatrix H I e₀ 0 i)) = _
  rw [actualGaussRulingMatrix_first_row_closed_normal H I e e₀ i]

include hY hh

/-- The original graph pivot remains nonzero after the actual
algebraic coefficient extension. -/
theorem extendedClosedGaussNormal_graph_pivot_ne_zero : (λ) ≠ 0 :=
  (map_ne_zero (algebraMap C₀ E)).mpr
    (actualClosedGaussNormalCovector_graph_pivot_ne_zero H I p hY h hh e)

/-- The first normal row of the original ruling equals the actual
graph-invariant covector times its exact original nonzero pivot. -/
theorem extendedClosedGaussRulingMatrix_first_row_eq_graph_pivot_mul
    (e₀ : RatFunc K ≃ₐ[K] G₀) (i : Fin 4) :
    extendedClosedGaussRulingMatrix H I E e₀ 0 i = (λ) * algebraMap C₀ E ((ν) i) := by
  rw [extendedClosedGaussRulingMatrix_first_row_closed_normal H I E e e₀ i,
    actualClosedGaussNormalCovector_eq_graph_pivot_mul H I p hY h hh e i, map_mul]

variable [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d) (hd : 0 < d)
    (hind : ¬ ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ν₀" => extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0
local notation "Q" => MvPolynomial.map (algebraMap C₀ E) (linearFormPolynomial (ν))

local instance nativeGraphNormalComparisonIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeGraphNormalComparisonAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The chosen actual native tangent plane has the same graph
normalization, without any supplied covector comparison. -/
theorem extendedClosedGaussChosenRulingMatrix_first_row_eq_graph_pivot_mul (i : Fin 4) :
    (ν₀) i = (λ) * algebraMap C₀ E ((ν) i) :=
  extendedClosedGaussRulingMatrix_first_row_eq_graph_pivot_mul H I p hY h hh E e
    (actualGaussRulingParameterChoice H I hH hd hind hGauss) i

/-- The actual chosen tangent-plane section has exactly the
constructed graph linear-form value times the proved nonzero pivot. -/
theorem extendedClosedGauss_chosen_plane_value_eq_graph_pivot_mul :
    (∑ i, algebraMap E (N).functionField ((ν₀) i) * (w) i) =
      algebraMap E (N).functionField (λ) * aeval (w) (Q) := by
  simp only [extendedClosedGaussChosenRulingMatrix_first_row_eq_graph_pivot_mul H I p hY h hh E e hH hd hind hGauss,
    map_mul, linearFormPolynomial, map_sum, MvPolynomial.map_C, MvPolynomial.map_X, aeval_C, aeval_X,
    Finset.mul_sum, mul_assoc]

/-- Dividing by the actual normal pivot identifies the constructed
graph form with the chosen native tangent-plane value. -/
theorem extendedClosedGauss_graph_value_eq_chosen_plane_div_pivot :
    aeval (w) (Q) = (∑ i, algebraMap E (N).functionField ((ν₀) i) * (w) i) /
      algebraMap E (N).functionField (λ) := by
  apply (eq_div_iff ((map_ne_zero (algebraMap E (N).functionField)).mpr
    (extendedClosedGaussNormal_graph_pivot_ne_zero H I p hY h hh E e))).mpr
  rw [extendedClosedGauss_chosen_plane_value_eq_graph_pivot_mul H I p hY h hh E e hH hd hind hGauss]
  exact mul_comm _ _

end DimensionFourDependence
