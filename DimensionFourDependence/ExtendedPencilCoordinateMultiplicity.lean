import DimensionFourDependence.AlgebraicCoordinateBaseChange
import DimensionFourDependence.PencilChartCoordinateMultiplicity
import DimensionFourDependence.ClosedGaussExtendedPencilCharts

/-! # Coordinate multiplicity on the actual pencil after coefficient extension

The chart is extended first and then normalized in its own fraction
field. Its original tensor coordinates and extended original equation
construct the same pencil-degree order bound at every height-one prime.
-/

namespace DimensionFourDependence

universe u

open MvPolynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]

local notation "C₀" => closedGaussParameterField H I
local notation "A₀" s:max => closedGaussPencilChartAlgebra H I s
local notation "Aₑ" s:max => E ⊗[C₀] A₀ s

/-- The original coordinate element in the actual extended pencil chart. -/
noncomputable def extendedGaussPencilChartCoordinate
    (s : Fin 4 ≃ Option (Fin 3)) (i : Fin 3) : Aₑ s :=
  (1 : E) ⊗ₜ[C₀] closedGaussPencilChartCoordinate H I s i

/-- Original coordinates still generate the entire chart after extending
its coefficient field. -/
theorem extendedGaussPencilChartCoordinate_adjoin
    (s : Fin 4 ≃ Option (Fin 3)) :
    Algebra.adjoin E (Set.range (extendedGaussPencilChartCoordinate H I E s)) = ⊤ :=
  tensor_coordinates_adjoin_eq_top (closedGaussPencilChartCoordinate H I s)
    (closedGaussPencilChartCoordinate_adjoin H I s)

/-- Original chart coordinates remain nonzero after coefficient extension. -/
theorem extendedGaussPencilChartCoordinate_ne_zero
    (s : Fin 4 ≃ Option (Fin 3)) (i : Fin 3) :
    extendedGaussPencilChartCoordinate H I E s i ≠ 0 :=
  tensor_coordinate_ne_zero (closedGaussPencilChartCoordinate_ne_zero H I s i)

/-- The coefficient-extended original pencil equation is still nonzero,
still vanishes at the original tensor coordinates, and still has degree
at most the original pencil degree. -/
theorem actual_extended_gauss_pencil_chart_equation_data
    (e : RatFunc K ≃ₐ[K] C₀) (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (s : Fin 4 ≃ Option (Fin 3)) :
    MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilChartEquation H I e p q s) ≠ 0 ∧
      aeval (extendedGaussPencilChartCoordinate H I E s)
        (MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilChartEquation H I e p q s)) = 0 ∧
      (MvPolynomial.map (algebraMap C₀ E)
        (closedGaussPencilChartEquation H I e p q s)).totalDegree ≤ D := by
  obtain ⟨hf0, hroot, hdegree⟩ := actual_closed_gauss_pencil_chart_equation_data
    H I e p q hq hrel hpH hqH ht s
  refine ⟨?_, tensor_coordinate_equation (E := E) _ _ hroot, ?_⟩
  · intro hzero
    apply hf0
    apply MvPolynomial.map_injective (algebraMap C₀ E) (algebraMap C₀ E).injective
    simpa only [map_zero] using hzero
  · have hmap : (MvPolynomial.map (algebraMap C₀ E)
        (closedGaussPencilChartEquation H I e p q s)).totalDegree ≤
        (closedGaussPencilChartEquation H I e p q s).totalDegree :=
      Finset.sup_mono (MvPolynomial.support_map_subset _ _)
    exact hmap.trans hdegree

variable [CharZero K]

/-- The actual coefficient-extended pencil chart is still a surface
over its extended coefficient field. -/
theorem actual_extended_gauss_pencil_chart_trdeg_two
    [Algebra.IsAlgebraic C₀ E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1) (s : Fin 4 ≃ Option (Fin 3)) :
    Algebra.trdeg E (Aₑ s) = 2 := by
  let : IsDomain (Aₑ s) := actual_closed_gauss_extended_chart_isDomain H I s E
  rw [algebraic_tensor_base_change_trdeg]
  exact actual_closed_gauss_pencil_chart_trdeg_two H hH I e hGauss s

/-- On the canonical normalization formed after any algebraic coefficient
extension, each original coordinate hyperplane has order at most the
original pencil degree at every height-one prime. -/
theorem actual_extended_gauss_pencil_chart_coordinate_order_le_degree
    [Algebra.IsAlgebraic C₀ E]
    {d : ℕ} (hH : IsHomogMap H d) (e : RatFunc K ≃ₐ[K] C₀)
    (hGauss : gaussImageDimension H I = 1)
    (p q : MvPolynomial (Fin 4) K) {D : ℕ}
    (hq : q ≠ 0) (hrel : IsRelPrime p q) (hpH : p.IsHomogeneous D) (hqH : q.IsHomogeneous D)
    (ht : closedGaussParameterSourceHom H I e RatFunc.X =
      algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) q)
    (s : Fin 4 ≃ Option (Fin 3)) (r : Fin 3 ≃ Option (Option Unit))
    (Q : Ideal (normalizationRing (Aₑ s))) [Q.IsPrime] (hQ : Q.height = 1)
    (hz : algebraMap (Aₑ s) (normalizationRing (Aₑ s))
      (extendedGaussPencilChartCoordinate H I E s (r.symm (some none))) ∈ Q)
    (a : ℕ) (horder : algebraMap (Aₑ s) (Localization.AtPrime Q)
      (extendedGaussPencilChartCoordinate H I E s (r.symm (some none))) ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ a) : a ≤ D := by
  let A := Aₑ s
  let : CharZero C₀ := charZero_of_injective_algebraMap (algebraMap K C₀).injective
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap C₀ E).injective
  let : Algebra.FiniteType C₀ (A₀ s) := closedGaussPencilChartAlgebra_finiteType H I s
  let : IsDomain A := actual_closed_gauss_extended_chart_isDomain H I s E
  let : Algebra.FiniteType E A := inferInstance
  let x : Option (Option Unit) → A := fun j => extendedGaussPencilChartCoordinate H I E s (r.symm j)
  let F := MvPolynomial.map (algebraMap C₀ E) (closedGaussPencilChartEquation H I e p q s)
  let f := MvPolynomial.renameEquiv E r F
  obtain ⟨hF0, hroot, hdegree⟩ := actual_extended_gauss_pencil_chart_equation_data
    H I E e p q hq hrel hpH hqH ht s
  have hx : Algebra.adjoin E (Set.range x) = ⊤ := by
    have hrange : Set.range x = Set.range (extendedGaussPencilChartCoordinate H I E s) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨r.symm i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨r i, by simp [x]⟩
    rw [hrange]
    exact extendedGaussPencilChartCoordinate_adjoin H I E s
  have hf : f ≠ 0 := by
    intro h
    apply hF0
    apply (MvPolynomial.renameEquiv E r).injective
    simpa only [map_zero] using h
  have hroot' : aeval x f = 0 := by
    change aeval x (rename r F) = 0
    rw [aeval_rename]
    have hcoords : x ∘ r = extendedGaussPencilChartCoordinate H I E s := by
      funext i
      simp [x]
    rw [hcoords]
    exact hroot
  have htr : 2 ≤ Algebra.trdeg E A := by
    rw [actual_extended_gauss_pencil_chart_trdeg_two H I E hH e hGauss s]
  have h := canonical_normalization_coordinate_order_le_totalDegree
    (k := E) x hx htr Q hQ
      (extendedGaussPencilChartCoordinate_ne_zero H I E s (r.symm (some none)))
      hz f hf hroot' a horder
  exact h.trans ((MvPolynomial.totalDegree_renameEquiv r F).le.trans hdegree)

end DimensionFourDependence
