import DimensionFourDependence.HomogeneousAffineLeadingCoefficient
import DimensionFourDependence.VertexPolynomialExpansion
import DimensionFourDependence.ProjectiveFiberEquations

/-! # The original highest vertex coefficient vanishes on the projected direction

For an original homogeneous polynomial P of degree D and vertex degree
J, substitution of affine-linear transverse coordinates and a quadratic
vertex coordinate has coefficient at D+J equal to the original J-th
vertex coefficient evaluated at the transverse direction, multiplied by
the J-th power of the quadratic vertex coefficient. Constancy therefore
forces that original coefficient to vanish at the direction.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K E sigma : Type*} [Field K] [Field E] [Algebra K E] [Finite sigma]

/-- The exact D+J coefficient after the original homogeneous
polynomial is evaluated on a parabola with the specified vertex axis. -/
theorem homogeneous_parabolic_vertex_highest_coefficient
    (P : MvPolynomial (Option sigma) K) (hP0 : P ≠ 0)
    {D : ℕ} (hP : P.IsHomogeneous D)
    (x A : sigma → E) (w : Polynomial E) (hw : w.natDegree ≤ 2) :
    (aeval (fun j : Option sigma => j.elim w
      (fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X)) P).coeff
        (D + P.degreeOf none) =
      w.coeff 2 ^ P.degreeOf none *
        aeval A ((optionEquivLeft K sigma P).coeff (P.degreeOf none)) := by
  classical
  let Q := optionEquivLeft K sigma P
  let J := P.degreeOf none
  let s : sigma → Polynomial E := fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X
  have hs (i : sigma) : (s i).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simp)
  have hJD : J ≤ D := (degreeOf_le_totalDegree P none).trans hP.totalDegree_le
  have hQ0 : Q ≠ 0 := by
    intro hz
    apply hP0
    apply (optionEquivLeft K sigma).injective
    exact hz.trans (map_zero _).symm
  have hQJ : Q.natDegree = J := natDegree_optionEquivLeft K P
  have hJmem : J ∈ Q.support := hQJ ▸ Polynomial.natDegree_mem_support_of_nonzero hQ0
  have hcoeffHom (j : ℕ) (hj : j ≤ D) : (Q.coeff j).IsHomogeneous (D - j) :=
    original_vertex_coefficient_isHomogeneous P hP j hj
  have hdeg (j : ℕ) (hj : j ≤ D) :
      (aeval s (Q.coeff j) * w ^ j).natDegree ≤ D + j := by
    have hleft : (aeval s (Q.coeff j)).natDegree ≤ D - j :=
      (polynomial_natDegree_aeval_le_totalDegree s hs _).trans (hcoeffHom j hj).totalDegree_le
    have hright : (w ^ j).natDegree ≤ j * 2 := Polynomial.natDegree_pow_le_of_le j hw
    exact Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add hleft hright).trans_eq (by omega))
  have hsum : (aeval (fun j : Option sigma => j.elim w s) P).coeff (D + J) =
      (aeval s (Q.coeff J) * w ^ J).coeff (D + J) := by
    rw [original_vertex_polynomial_evaluation_expansion, Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_single_of_mem J hJmem
    intro j hj hne
    have hjJ : j ≤ J := (Polynomial.le_natDegree_of_mem_supp j hj).trans_eq hQJ
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((hdeg j (hjJ.trans hJD)).trans_lt (by omega))
  change (aeval (fun j : Option sigma => j.elim w s) P).coeff (D + J) = _
  rw [hsum]
  have hN : D + J = (D - J) + J * 2 := by omega
  rw [hN, Polynomial.coeff_mul_add_eq_of_natDegree_le
    ((polynomial_natDegree_aeval_le_totalDegree s hs _).trans (hcoeffHom J hJD).totalDegree_le)
    (Polynomial.natDegree_pow_le_of_le J hw)]
  rw [homogeneous_affine_line_coefficient_at_degree _ (hcoeffHom J hJD),
    Polynomial.coeff_pow_of_natDegree_le hw]
  exact mul_comm _ _

/-- Constancy on the formal parabola makes the original highest
vertex coefficient vanish at its projected affine direction. -/
theorem constant_parabolic_polynomial_highest_vertex_coefficient_vanishes
    (P : MvPolynomial (Option sigma) K) (hP0 : P ≠ 0)
    {D : ℕ} (hP : P.IsHomogeneous D) (hJ : 0 < P.degreeOf none)
    (x A : sigma → E) (w : Polynomial E) (hw : w.natDegree ≤ 2) (hw2 : w.coeff 2 ≠ 0)
    (c : E) (hconstant : aeval (fun j : Option sigma => j.elim w
      (fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X)) P = Polynomial.C c) :
    aeval A ((optionEquivLeft K sigma P).coeff (P.degreeOf none)) = 0 := by
  have he := congrArg (fun q : Polynomial E => q.coeff (D + P.degreeOf none)) hconstant
  rw [homogeneous_parabolic_vertex_highest_coefficient P hP0 hP x A w hw] at he
  have hc : (Polynomial.C c).coeff (D + P.degreeOf none) = 0 := by
    exact Polynomial.coeff_C_of_ne_zero (by omega)
  rw [hc] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hw2)

/-- The direction lies on a fixed proper nonconstant original-field
homogeneous polynomial locus supplied by the actual highest vertex coefficient. -/
theorem constant_parabolic_polynomial_constructs_proper_direction_equation
    (P : MvPolynomial (Option sigma) K) (hP0 : P ≠ 0)
    {D : ℕ} (hP : P.IsHomogeneous D) (hJ : 0 < P.degreeOf none)
    (x A : sigma → E) (w : Polynomial E) (hw : w.natDegree ≤ 2) (hw2 : w.coeff 2 ≠ 0)
    (c : E) (hconstant : aeval (fun j : Option sigma => j.elim w
      (fun i => Polynomial.C (x i) + Polynomial.C (A i) * Polynomial.X)) P = Polynomial.C c) :
    let Q := (optionEquivLeft K sigma P).coeff (P.degreeOf none)
    Q ≠ 0 ∧ Q.IsHomogeneous (D - P.degreeOf none) ∧ 0 < Q.totalDegree ∧ aeval A Q = 0 := by
  let Q := (optionEquivLeft K sigma P).coeff (P.degreeOf none)
  have hQ0 : Q ≠ 0 := by
    have hP' : optionEquivLeft K sigma P ≠ 0 := by
      intro hz
      exact hP0 ((optionEquivLeft K sigma).injective (hz.trans (map_zero _).symm))
    simpa only [Q, ← natDegree_optionEquivLeft K P, Polynomial.coeff_natDegree] using
      Polynomial.leadingCoeff_ne_zero.mpr hP'
  have hzero := constant_parabolic_polynomial_highest_vertex_coefficient_vanishes
    P hP0 hP hJ x A w hw hw2 c hconstant
  exact ⟨hQ0, original_vertex_coefficient_isHomogeneous P hP _
    ((degreeOf_le_totalDegree P none).trans hP.totalDegree_le),
    totalDegree_pos_of_aeval_zero A Q hQ0 hzero, hzero⟩

end DimensionFourDependence
