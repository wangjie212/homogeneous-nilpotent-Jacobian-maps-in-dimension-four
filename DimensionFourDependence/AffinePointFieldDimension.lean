import DimensionFourDependence.AffineGeneratedPointCoordinates
import DimensionFourDependence.MovingPlanePointFieldDimension

/-! # The moving-plane criterion in the actual generated affine point field -/

namespace DimensionFourDependence

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- A family field of dimension at least two, algebraic over its actual
affine point coordinates and parameter, has the same dimension as that
point field when the point lies in a plane family with at most a fixed
projective point. The point field, projective frame, and its generation
are constructed from the given affine values. -/
theorem affine_point_field_dimension_of_moving_plane
    (y : Fin 3 → L) (s : Fin 4 ≃ Option (Fin 3))
    (v : Fin 4 → Polynomial K)
    (hdim : Module.finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (t : L)
    [Algebra.IsAlgebraic (IntermediateField.adjoin (IntermediateField.adjoin K (Set.range y)) {t}) L]
    (hL : 2 ≤ Algebra.trdeg K L)
    (hplane : ∑ i, (s i).elim 1 y * Polynomial.aeval t (v i) = 0) :
    IsAlgebraic (IntermediateField.adjoin K (Set.range y)) t ∧
      Algebra.trdeg K (IntermediateField.adjoin K (Set.range y)) = Algebra.trdeg K L ∧
      2 ≤ Algebra.trdeg K (IntermediateField.adjoin K (Set.range y)) := by
  let F := IntermediateField.adjoin K (Set.range y)
  let x := affineGeneratedPointCoordinate (K := K) y s
  have hx (i : Fin 4) : algebraMap F L (x i) = (s i).elim 1 y := by
    change ((affineGeneratedPointCoordinate (K := K) y s i) : L) = _
    cases hsi : s i <;> simp [affineGeneratedPointCoordinate, hsi]
  have hp : ∑ i, algebraMap F L (x i) * Polynomial.aeval t (v i) = 0 := by
    simpa only [hx] using hplane
  have ha : x (s.symm none) ≠ 0 := by
    rw [show x (s.symm none) = 1 from affineGeneratedPointCoordinate_pivot (K := K) y s]
    exact one_ne_zero
  have h := polynomial_moving_plane_incidence_point_field_dimension v hdim t hL x
    (s.symm none) ha (affineGeneratedPointCoordinate_chartField_top y s) hp
  exact ⟨h.1, h.2, hL.trans_eq h.2.symm⟩

end DimensionFourDependence
