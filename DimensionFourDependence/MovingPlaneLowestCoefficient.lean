import DimensionFourDependence.VertexPolynomialExpansion
import DimensionFourDependence.AlgebraicProjectiveLineRoots

/-! # A moving line cannot lie in a fixed proper ternary homogeneous locus

Choose the lowest nonzero coefficient in the first original coordinate.
Its coefficient in the affine moving-line restriction is its binary
homogeneous value at the line-coefficient ratio. A transcendental ratio
cannot be a root of that nonzero original binary polynomial. Thus the
entire original moving-line restriction is nonzero.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K E sigma : Type*} [Field K] [Field E] [Algebra K E]

/-- Taking constant coefficients commutes with original polynomial
evaluation at polynomial coordinates. -/
theorem polynomial_coordinate_aeval_constant_coefficient
    (P : MvPolynomial sigma K) (s : sigma → Polynomial E) :
    (aeval s P).coeff 0 = aeval (fun i => (s i).coeff 0) P := by
  have hzero (q : Polynomial E) : Polynomial.aeval (0 : E) q = q.coeff 0 := by
    simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero]
  have he := comp_aeval_apply s ((Polynomial.aeval (0 : E)).restrictScalars K) P
  simpa only [AlgHom.restrictScalars_apply, hzero] using he

/-- The lowest original nonzero vertex coefficient gives the exact
lowest coefficient after arbitrary polynomial substitutions in the
other coordinates, with the vertex coordinate left as X. -/
theorem original_vertex_restriction_lowest_coefficient
    (P : MvPolynomial (Option sigma) K) (s : sigma → Polynomial E) (j : ℕ)
    (hj : j ∈ (optionEquivLeft K sigma P).support)
    (hmin : ∀ i ∈ (optionEquivLeft K sigma P).support, j ≤ i) :
    (aeval (fun o : Option sigma => o.elim Polynomial.X s) P).coeff j =
      aeval (fun i => (s i).coeff 0) ((optionEquivLeft K sigma P).coeff j) := by
  classical
  rw [original_vertex_polynomial_evaluation_expansion, Polynomial.finsetSum_coeff]
  calc
    (∑ i ∈ (optionEquivLeft K sigma P).support,
        (aeval s ((optionEquivLeft K sigma P).coeff i) * Polynomial.X ^ i).coeff j) =
        (aeval s ((optionEquivLeft K sigma P).coeff j) * Polynomial.X ^ j).coeff j := by
      apply Finset.sum_eq_single_of_mem j hj
      intro i hi hne
      rw [Polynomial.coeff_mul_X_pow', ite_eq_right (by have := hmin i hi; omega)]
    _ = (aeval s ((optionEquivLeft K sigma P).coeff j)).coeff 0 := by
      simpa only [zero_add] using
        Polynomial.coeff_mul_X_pow (aeval s ((optionEquivLeft K sigma P).coeff j)) j 0
    _ = _ := polynomial_coordinate_aeval_constant_coefficient _ _

variable [Infinite K]

/-- A nonzero fixed original homogeneous ternary equation restricts
nontrivially to a line whose specified coefficient ratio is transcendental. -/
theorem transcendental_moving_plane_affine_restriction_ne_zero
    (a b : E) (ha : Transcendental K a)
    (P : MvPolynomial (Option (Fin 2)) K) (hP0 : P ≠ 0)
    {D : ℕ} (hP : P.IsHomogeneous D) :
    aeval (fun o : Option (Fin 2) => o.elim Polynomial.X
      (![1, Polynomial.C a + Polynomial.C b * Polynomial.X] : Fin 2 → Polynomial E)) P ≠ 0 := by
  classical
  let Q := optionEquivLeft K (Fin 2) P
  have hQ0 : Q ≠ 0 := by
    intro hz
    exact hP0 ((optionEquivLeft K (Fin 2)).injective (hz.trans (map_zero _).symm))
  have hsupport : Q.support.Nonempty := Polynomial.support_nonempty.mpr hQ0
  let j := Q.support.min' hsupport
  have hj : j ∈ Q.support := Finset.min'_mem Q.support hsupport
  have hmin : ∀ i ∈ Q.support, j ≤ i := fun i hi => Finset.min'_le Q.support i hi
  have hjD : j ≤ D :=
    (Polynomial.le_natDegree_of_mem_supp j hj).trans
      ((natDegree_optionEquivLeft K P).trans_le ((degreeOf_le_totalDegree P none).trans hP.totalDegree_le))
  have hpj : Q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hpjhom : (Q.coeff j).IsHomogeneous (D - j) :=
    original_vertex_coefficient_isHomogeneous P hP j hjD
  let R : Polynomial K := aeval (![1, Polynomial.X] : Fin 2 → Polynomial K) (Q.coeff j)
  have hR0 : R ≠ 0 := homogeneous_binary_affine_chart_ne_zero _ hpjhom hpj
  have hvalue : aeval (![1, a] : Fin 2 → E) (Q.coeff j) ≠ 0 := by
    intro hz
    have he := comp_aeval_apply (![1, Polynomial.X] : Fin 2 → Polynomial K)
      (Polynomial.aeval a) (Q.coeff j)
    have hpoint : (fun i : Fin 2 => Polynomial.aeval a
        ((![1, Polynomial.X] : Fin 2 → Polynomial K) i)) = (![1, a] : Fin 2 → E) := by
      funext i
      fin_cases i <;> simp
    rw [hpoint, hz] at he
    apply hR0
    apply (transcendental_iff_injective.mp ha)
    exact he.trans (map_zero (Polynomial.aeval a)).symm
  let s : Fin 2 → Polynomial E := ![1, Polynomial.C a + Polynomial.C b * Polynomial.X]
  have hpoint0 : (fun i => (s i).coeff 0) = (![1, a] : Fin 2 → E) := by
    funext i
    fin_cases i <;> simp [s]
  have hc := original_vertex_restriction_lowest_coefficient P s j hj hmin
  rw [hpoint0] at hc
  intro hz
  have hc0 := congrArg (fun q : Polynomial E => q.coeff j) hz
  rw [hc] at hc0
  exact hvalue (hc0.trans (Polynomial.coeff_zero j))

end DimensionFourDependence
