import DimensionFourDependence.PolynomialPlaneParameterRigidity
import DimensionFourDependence.GeneratedFieldDimension

/-! # Moving-plane incidence forces a two-dimensional source point field -/

namespace DimensionFourDependence

open Matrix Module

universe u

variable {K E L : Type u} [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]

/-- If the full family field is algebraic over the source point
field and one parameter, and has dimension at least two, incidence in a
plane family with no fixed curve forces the parameter algebraic over the
point field and preserves the full field dimension there. -/
theorem polynomial_moving_plane_incidence_point_field_dimension
    (v : Fin 4 → Polynomial K)
    (hdim : finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (t : L) [Algebra.IsAlgebraic (IntermediateField.adjoin E {t}) L]
    (hL : 2 ≤ Algebra.trdeg K L)
    (x : Fin 4 → E) (a : Fin 4) (ha : x a ≠ 0)
    (hgen : projectiveCoordinateChartField (C := K) x a = ⊤)
    (hplane : ∑ i, algebraMap E L (x i) * Polynomial.aeval t (v i) = 0) :
    IsAlgebraic E t ∧ Algebra.trdeg K E = Algebra.trdeg K L := by
  let J := IntermediateField.adjoin E {t}
  let : IsScalarTower K J L := IsScalarTower.of_algebraMap_eq (by
    intro c
    rw [IsScalarTower.algebraMap_apply K E J, ← IsScalarTower.algebraMap_apply E J L]
    exact IsScalarTower.algebraMap_apply K E L c)
  have hJL : Algebra.trdeg J L = 0 := trdeg_eq_zero
  have hEJ : Algebra.trdeg E J ≤ 1 := generatedField_singleton_trdeg_le_one t
  have hEpos : Algebra.trdeg K E ≠ 0 := by
    intro hEzero
    have hKJ := trdeg_add_eq (A := J) K E
    have hKJle : Algebra.trdeg K J ≤ 1 := by
      rw [← hKJ, hEzero, zero_add]
      exact hEJ
    have hKJL := trdeg_add_eq (A := L) K J
    have hKLle : Algebra.trdeg K L ≤ 1 := by
      rw [← hKJL, hJL, add_zero]
      exact hKJle
    have hbad : (2 : Cardinal) ≤ 1 := hL.trans hKLle
    norm_num at hbad
  have hcoord : Algebra.trdeg K (projectiveCoordinateChartField (C := K) x a) = Algebra.trdeg K E := by
    rw [hgen]
    exact (IntermediateField.topEquiv : (⊤ : IntermediateField K E) ≃ₐ[K] E).trdeg_eq
  have ht : IsAlgebraic E t := polynomial_plane_parameter_isAlgebraic_over_nonconstant_point
    v hdim x t hplane a ha (fun hz => hEpos (hcoord.symm.trans hz))
  let : Algebra.IsAlgebraic E J := IntermediateField.isAlgebraic_adjoin_simple ht.isIntegral
  have hEJzero : Algebra.trdeg E J = 0 := trdeg_eq_zero
  have hEJL := trdeg_add_eq (A := L) E J
  rw [hEJzero, hJL, zero_add] at hEJL
  have hKEL := trdeg_add_eq (A := L) K E
  rw [← hEJL, add_zero] at hKEL
  exact ⟨ht, hKEL⟩

/-- In a two-dimensional family field, the actual source point
field has dimension two under these hypotheses, rather than the
dimension-one field of a fixed source curve. -/
theorem polynomial_moving_plane_incidence_source_point_trdeg_two
    (v : Fin 4 → Polynomial K)
    (hdim : finrank K (LinearMap.ker (polynomialCovectorCoefficientMatrix v).toLin') ≤ 1)
    (t : L) [Algebra.IsAlgebraic (IntermediateField.adjoin E {t}) L]
    (hL : Algebra.trdeg K L = 2)
    (x : Fin 4 → E) (a : Fin 4) (ha : x a ≠ 0)
    (hgen : projectiveCoordinateChartField (C := K) x a = ⊤)
    (hplane : ∑ i, algebraMap E L (x i) * Polynomial.aeval t (v i) = 0) :
    Algebra.trdeg K E = 2 :=
  (polynomial_moving_plane_incidence_point_field_dimension v hdim t (by rw [hL]) x a ha hgen hplane).2.trans hL

end DimensionFourDependence
