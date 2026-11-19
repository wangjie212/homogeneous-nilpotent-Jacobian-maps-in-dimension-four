import DimensionFourDependence.GaussParameterSurfaceDimension

/-! # Full-dimensional actual coefficient embeddings give algebraic extensions -/

namespace DimensionFourDependence

universe u
variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F]
attribute [local instance] coefficientFieldScalarTower

/-- An actual embedding of the algebraic coefficient field into an
ambient field of the same finite absolute dimension makes the ambient
extension algebraic. No compatibility with a separately chosen output
field embedding is required. -/
theorem coefficient_extension_isAlgebraic_of_absolute_dimension_le
    {n : ℕ} (Y : Fin n → F) (hY : AlgebraicIndependent K Y)
    (κ : Type u) [Field κ] [Algebra (coefficientField (K := K) Y) κ]
    [Algebra K κ] [IsScalarTower K (coefficientField (K := K) Y) κ]
    (htr : Algebra.trdeg K κ ≤ n) :
    Algebra.IsAlgebraic (coefficientField (K := K) Y) κ := by
  have he := trdeg_add_eq (A := κ) K (coefficientField (K := K) Y)
  rw [independent_output_coefficientField_absolute_trdeg Y hY] at he
  have hn : (n : Cardinal) ≤ Algebra.trdeg K κ := by
    rw [← he]
    exact self_le_add_right _ _
  have heq := le_antisymm htr hn
  rw [heq] at he
  apply trdeg_eq_zero_iff.mp
  rcases Cardinal.add_eq_left_iff.mp he with h | h
  · exact False.elim ((not_le_of_gt (Cardinal.natCast_lt_aleph0 (n := n)))
      ((le_max_left _ _).trans h))
  · exact h

end DimensionFourDependence
