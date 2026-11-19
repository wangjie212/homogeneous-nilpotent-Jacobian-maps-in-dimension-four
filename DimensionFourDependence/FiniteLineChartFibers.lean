import DimensionFourDependence.FiniteLinesAtSmoothPoint

/-! # Finite fibers in the actual matrix parameter charts

A matrix chart represents each line injectively. Consequently the finite
set of lines through a smooth point gives a finite set of chart parameters
through that point, in every coordinate-permuted chart of the image.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix Module

variable {F : Type*} [Field F]

/-- Distinct matrices in the graph chart represent distinct actual projective lines. -/
theorem graphLineFour_injective : Function.Injective (graphLineFour (F := F)) := by
  intro B C he
  change (graphLine B).map (fourCoordinateEquiv (F := F)).toLinearMap =
    (graphLine C).map (fourCoordinateEquiv (F := F)).toLinearMap at he
  have hg := (Submodule.map_injective_of_injective
    (f := (fourCoordinateEquiv (F := F)).toLinearMap) fourCoordinateEquiv.injective) he
  ext i j
  have hm : (Pi.single j 1, B *ᵥ Pi.single j 1) ∈ graphLine C := by
    rw [← hg]
    rfl
  have hv := congrFun ((mem_graphLine C _).mp hm) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hv

/-- The four-coordinate line represented by an arbitrary point of a fixed permuted chart. -/
def lineChartMemberLine (p : Equiv.Perm (Fin 4)) (B : Matrix (Fin 2) (Fin 2) F) :
    Submodule F (Fin 4 → F) :=
  (graphLineFour B).map (lineCoordinatePermutation (F := F) p).symm.toLinearMap

/-- Each coordinate-permuted matrix chart is injective on represented lines. -/
theorem lineChartMemberLine_injective (p : Equiv.Perm (Fin 4)) :
    Function.Injective (lineChartMemberLine (F := F) p) := by
  intro B C he
  apply graphLineFour_injective
  exact (Submodule.map_injective_of_injective
    (f := (lineCoordinatePermutation (F := F) p).symm.toLinearMap)
    (lineCoordinatePermutation (F := F) p).symm.injective) he

/-- Finiteness of geometric lines implies finiteness of their actual chart parameters. -/
theorem finite_line_chart_fiber_of_finite_contained_lines
    (R : MvPolynomial (Fin 4) F) (O : Fin 4 → F)
    (hfinite : {L : Submodule F (Fin 4 → F) | finrank F L = 2 ∧ O ∈ L ∧
      (∀ x ∈ L, aeval x R = 0)}.Finite) (p : Equiv.Perm (Fin 4)) :
    {B : Matrix (Fin 2) (Fin 2) F | B ∈ hypersurfaceLineChart (rename p.symm R) ∧
      O ∈ lineChartMemberLine p B}.Finite := by
  apply (Set.Finite.preimage (lineChartMemberLine_injective p).injOn hfinite).subset
  intro B hB
  change finrank F (lineChartMemberLine p B) = 2 ∧ O ∈ lineChartMemberLine p B ∧
    (∀ x ∈ lineChartMemberLine p B, aeval x R = 0)
  refine ⟨?_, hB.2, ?_⟩
  · rw [lineChartMemberLine, LinearEquiv.finrank_map_eq, graphLineFour_finrank]
  · exact hypersurfaceAtlasLine_contained R ⟨p, ⟨B, hB.1⟩⟩

variable [CharZero F]

/-- The parameter fiber of every line chart over a smooth point of an
irreducible nonlinear homogeneous hypersurface is finite. -/
theorem irreducible_hypersurface_finite_line_chart_fiber
    (R : MvPolynomial (Fin 4) F) {d : ℕ} (hd : 2 ≤ d)
    (hR : R.IsHomogeneous d) (hirred : Irreducible R)
    (O : Fin 4 → F) (hO : O ≠ 0) (hzero : aeval O R = 0)
    (hsmooth : (fun i => aeval O (pderiv i R)) ≠ 0) (p : Equiv.Perm (Fin 4)) :
    {B : Matrix (Fin 2) (Fin 2) F | B ∈ hypersurfaceLineChart (rename p.symm R) ∧
      O ∈ lineChartMemberLine p B}.Finite := by
  exact finite_line_chart_fiber_of_finite_contained_lines R O
    (irreducible_hypersurface_finite_lines_at_smooth_point R hd hR hirred O hO hzero hsmooth) p

/-- For the actual nonplanar image equation, every matrix chart has a
finite parameter fiber over every smooth projective point. -/
theorem ImageRelationWitness.finite_line_chart_fiber
    (H : Fin 4 → MvPolynomial (Fin 4) F) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hind : ¬ ComponentsDependent H) (I : ImageRelationWitness H)
    (O : Fin 4 → F) (hO : O ≠ 0) (hzero : aeval O I.equation = 0)
    (hsmooth : (fun i => aeval O (pderiv i I.equation)) ≠ 0) (p : Equiv.Perm (Fin 4)) :
    {B : Matrix (Fin 2) (Fin 2) F | B ∈ hypersurfaceLineChart (rename p.symm I.equation) ∧
      O ∈ lineChartMemberLine p B}.Finite := by
  exact finite_line_chart_fiber_of_finite_contained_lines I.equation O
    (I.finite_lines_at_smooth_point H hd hH hind O hO hzero hsmooth) p

end DimensionFourDependence
