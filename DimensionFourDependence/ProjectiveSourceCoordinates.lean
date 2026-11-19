import DimensionFourDependence.ProjectiveSourceParameterField

/-! # Free affine coordinates on the original projective source

On each standard projective source chart the three original coordinate
ratios are algebraically independent over the original coefficient field.
Their actual coordinate algebra is the polynomial ring in three variables,
and it sits in the same actual projective source function field as the
closed Gauss pencil chart.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

local notation "R₄" => MvPolynomial (Fin 4) K
local notation "F₄" => FractionRing (MvPolynomial (Fin 4) K)

/-- Reindexing the original source coordinates preserves their complete
algebraic independence over the original coefficient field. -/
theorem projective_source_reindexed_evaluation_injective
    (s : Fin 4 ≃ Option (Fin 3)) :
    Function.Injective (aeval (fun j => rationalCoordinate (K := K) (s.symm j)) :
      MvPolynomial (Option (Fin 3)) K →ₐ[K] F₄) := by
  have h : (aeval (fun j => rationalCoordinate (K := K) (s.symm j)) :
      MvPolynomial (Option (Fin 3)) K →ₐ[K] F₄) =
      (Algebra.algHom K R₄ F₄).comp (renameEquiv K s.symm).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [aeval_X]
    change algebraMap R₄ F₄ (X (s.symm j)) = algebraMap R₄ F₄ (rename s.symm (X j))
    rw [rename_X]
  rw [h]
  exact (IsFractionRing.injective R₄ F₄).comp (renameEquiv K s.symm).injective

/-- The standard affine projective source chart has no polynomial
relations over the original coefficient field. -/
theorem projective_source_chart_vanishing_ideal_eq_bot
    (s : Fin 4 ≃ Option (Fin 3)) :
    fiberVanishingIdeal (L := K) (closedGaussPencilChartPoint (K := K) s) = ⊥ := by
  have hx : rationalCoordinate (K := K) (s.symm none) ≠ 0 := by
    simpa only [rationalCoordinate, map_zero] using
      (IsFractionRing.injective R₄ F₄).ne (X_ne_zero (s.symm none))
  have hker : RingHom.ker (aeval (fun j => rationalCoordinate (K := K) (s.symm j)) :
      MvPolynomial (Option (Fin 3)) K →ₐ[K] F₄) = Ideal.span {0} := by
    simpa using (RingHom.injective_iff_ker_eq_bot _).mp (projective_source_reindexed_evaluation_injective s)
  have h := homogeneous_principal_source_chart_relation_ideal (C := K)
    (fun j => rationalCoordinate (K := K) (s.symm j)) hx
    (0 : MvPolynomial (Option (Fin 3)) K) (MvPolynomial.isHomogeneous_zero _ _ 0) hker
  change fiberVanishingIdeal (L := K)
    (fun i : Fin 3 => rationalCoordinate (K := K) (s.symm (some i)) /
      rationalCoordinate (K := K) (s.symm none)) = ⊥
  simpa using h

/-- Evaluation at the three source chart ratios is injective. -/
theorem projective_source_chart_evaluation_injective
    (s : Fin 4 ≃ Option (Fin 3)) :
    Function.Injective (aeval (closedGaussPencilChartPoint (K := K) s) :
      MvPolynomial (Fin 3) K →ₐ[K] F₄) :=
  (RingHom.injective_iff_ker_eq_bot _).mpr (projective_source_chart_vanishing_ideal_eq_bot s)

/-- The actual three-ratio source chart coordinate ring is the polynomial
ring over the original field, with its original coordinate values. -/
noncomputable def projectiveSourceChartCoordinateEquiv
    (s : Fin 4 ≃ Option (Fin 3)) :
    MvPolynomial (Fin 3) K ≃ₐ[K]
      fiberCoordinateAlgebra (L := K) (closedGaussPencilChartPoint (K := K) s) :=
  (AlgEquiv.ofInjective (aeval (closedGaussPencilChartPoint (K := K) s))
    (projective_source_chart_evaluation_injective s)).trans
      (Subalgebra.equivOfEq _ _
        (Algebra.adjoin_range_eq_range_aeval K (closedGaussPencilChartPoint (K := K) s)).symm)

/-- Including the chart coordinate equal to one does not change the
actual original-coefficient source chart algebra. -/
theorem projective_source_three_ratio_algebra_eq
    (s : Fin 4 ≃ Option (Fin 3)) :
    fiberCoordinateAlgebra (L := K) (closedGaussPencilChartPoint (K := K) s) =
      projectiveCoordinateChartAlgebra (C := K) (rationalCoordinate (K := K) (n := 4)) (s.symm none) := by
  have hx : rationalCoordinate (K := K) (s.symm none) ≠ 0 := by
    simpa only [rationalCoordinate, map_zero] using
      (IsFractionRing.injective R₄ F₄).ne (X_ne_zero (s.symm none))
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact projectiveCoordinateChartAlgebra_ratio_mem (C := K) _ _ _
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    dsimp only
    rcases hsi : s i with _ | j
    · have hi : i = s.symm none := by rw [← hsi, s.symm_apply_apply]
      rw [hi, div_self hx]
      exact Subalgebra.one_mem _
    · have hi : i = s.symm (some j) := by rw [← hsi, s.symm_apply_apply]
      rw [hi]
      exact Algebra.subset_adjoin ⟨j, rfl⟩

/-- Polynomial coordinates identify the entire actual source chart
algebra, including the coordinate equal to one. -/
noncomputable def projectiveSourceFullChartCoordinateEquiv
    (s : Fin 4 ≃ Option (Fin 3)) :
    MvPolynomial (Fin 3) K ≃ₐ[K] projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none) :=
  (projectiveSourceChartCoordinateEquiv s).trans
    (Subalgebra.equivOfEq _ _ (projective_source_three_ratio_algebra_eq s))

/-- The coordinate isomorphism preserves each original ratio-valued
polynomial as a rational function in the source. -/
theorem projectiveSourceFullChartCoordinateEquiv_source
    (s : Fin 4 ≃ Option (Fin 3)) (r : MvPolynomial (Fin 3) K) :
    (projectiveSourceFullChartCoordinateEquiv s r : F₄) =
      aeval (closedGaussPencilChartPoint (K := K) s) r := by
  change (((AlgEquiv.ofInjective
    (aeval (closedGaussPencilChartPoint (K := K) s) : MvPolynomial (Fin 3) K →ₐ[K] F₄)
    (projective_source_chart_evaluation_injective s)) r) : F₄) = _
  exact AlgEquiv.ofInjective_apply _ _ r

/-- The original projective source function field carries the actual
three-variable polynomial coordinate action of its chosen chart. -/
@[instance_reducible]
noncomputable def projectiveSourceChartFieldAlgebra
    (s : Fin 4 ≃ Option (Fin 3)) :
    Algebra (MvPolynomial (Fin 3) K) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) :=
  ((algebraMap (projectiveCoordinateChartAlgebra (C := K) (rationalCoordinate (K := K) (n := 4)) (s.symm none))
      (projectiveCoordinateChartField (C := K) (rationalCoordinate (K := K) (n := 4)) (s.symm none))).comp
    (projectiveSourceFullChartCoordinateEquiv s).toRingHom).toAlgebra

/-- The original projective chart field is an actual fraction field of
the three-variable source chart polynomial ring. -/
theorem projective_source_chart_field_isFractionRing
    (s : Fin 4 ≃ Option (Fin 3)) :
    letI : Algebra (MvPolynomial (Fin 3) K) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) := projectiveSourceChartFieldAlgebra s
    IsFractionRing (MvPolynomial (Fin 3) K) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) := by
  let : Algebra (MvPolynomial (Fin 3) K) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) := projectiveSourceChartFieldAlgebra s
  exact IsFractionRing.of_ringEquiv_left (projectiveSourceFullChartCoordinateEquiv s).toRingEquiv
    (by intro r; rfl)

/-- The chart polynomial action agrees with the original coefficient
field action on the actual projective source function field. -/
theorem projective_source_chart_field_base_scalarTower
    (s : Fin 4 ≃ Option (Fin 3)) :
    letI : Algebra (MvPolynomial (Fin 3) K) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) := projectiveSourceChartFieldAlgebra s
    IsScalarTower K (MvPolynomial (Fin 3) K) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) := by
  let : Algebra (MvPolynomial (Fin 3) K) (projectiveCoordinateChartField (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none)) := projectiveSourceChartFieldAlgebra s
  apply IsScalarTower.of_algebraMap_eq
  intro c
  apply Subtype.ext
  change algebraMap K F₄ c =
    (projectiveSourceFullChartCoordinateEquiv s (algebraMap K (MvPolynomial (Fin 3) K) c) : F₄)
  rw [(projectiveSourceFullChartCoordinateEquiv s).commutes]
  rfl

end DimensionFourDependence
