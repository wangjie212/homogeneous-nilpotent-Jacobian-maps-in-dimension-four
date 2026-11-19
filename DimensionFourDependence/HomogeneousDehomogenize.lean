import DimensionFourDependence.HomogenizeChart
import DimensionFourDependence.HomogeneousResidueSpecialization

/-! # Dehomogenization on a fixed homogeneous degree is injective

Evaluation at the generic projective ratios recovers a homogeneous
polynomial after multiplication by the appropriate coordinate power.
Thus a homogeneous form is determined by its dehomogenization. This
also reconstructs it by homogenizing back to its prescribed degree.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K σ : Type*} [Field K]

/-- A homogeneous form vanishing on its affine chart is zero in the
original homogeneous polynomial ring. -/
theorem homogeneous_dehomogenize_eq_zero
    (P : MvPolynomial (Option σ) K) {d : ℕ} (hP : P.IsHomogeneous d)
    (hz : projectiveDehomogenize P = 0) : P = 0 := by
  let F := FractionRing (MvPolynomial (Option σ) K)
  let x : Option σ → F := fun j => algebraMap (MvPolynomial (Option σ) K) F (X j)
  have hx : x none ≠ 0 := by
    simpa only [x, map_zero] using
      (IsFractionRing.injective (MvPolynomial (Option σ) K) F).ne (X_ne_zero none)
  let z : Option σ → F := fun j => j.elim 1 (fun i => x (some i) / x none)
  have he := homogeneous_aeval_scale_indexed P hP z (x none)
  have hpoint : (fun j => x none * z j) = x := by
    funext j
    cases j with
    | none => simp [z]
    | some i =>
      change x none * (x (some i) / x none) = x (some i)
      exact mul_div_cancel₀ (x (some i)) hx
  have hchart : aeval z P = 0 := by
    rw [show z = (fun j : Option σ => j.elim 1 (fun i => x (some i) / x none)) from rfl,
      aeval_projectiveDehomogenize, hz, map_zero]
  rw [hpoint, hchart, mul_zero] at he
  have hmap : (aeval x : MvPolynomial (Option σ) K →ₐ[K] F) =
      IsScalarTower.toAlgHom K (MvPolynomial (Option σ) K) F := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [x]
  rw [hmap] at he
  exact IsFractionRing.injective (MvPolynomial (Option σ) K) F (by simpa using he)

/-- Two forms of the same homogeneous degree with equal chart
polynomials are equal in the original homogeneous coordinates. -/
theorem homogeneous_dehomogenize_injective
    (P Q : MvPolynomial (Option σ) K) {d : ℕ}
    (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous d)
    (h : projectiveDehomogenize P = projectiveDehomogenize Q) : P = Q := by
  apply sub_eq_zero.mp
  apply homogeneous_dehomogenize_eq_zero (P - Q) (hP.sub hQ)
  rw [map_sub, h, sub_self]

/-- Homogenizing a chart polynomial back to the prescribed degree
recovers the original homogeneous form, including powers of the chart coordinate. -/
theorem homogeneous_homogenize_dehomogenize
    (P : MvPolynomial (Option σ) K) {d : ℕ} (hP : P.IsHomogeneous d) :
    projectiveHomogenize (projectiveDehomogenize P) d = P := by
  have hd : (projectiveDehomogenize P).totalDegree ≤ d := by
    by_cases hp : P = 0
    · simp [hp]
    · exact (projectiveDehomogenize_totalDegree P).trans (hP.totalDegree hp).le
  apply homogeneous_dehomogenize_injective _ _ (projectiveHomogenize_isHomogeneous _ _ hd) hP
  exact projectiveDehomogenize_homogenize _ _

end DimensionFourDependence
