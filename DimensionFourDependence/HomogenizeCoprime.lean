import DimensionFourDependence.MultivariateHomogenize

/-! # Relative primality after homogenizing to actual degrees -/

namespace DimensionFourDependence

open MvPolynomial

variable {R σ : Type*} [Field R]

/-- A factor of an actual-degree homogenization that becomes a unit on
the affine chart was already a unit. Degree comparison excludes any
nonconstant factor that disappears on that chart. -/
theorem homogenization_factor_isUnit {p : MvPolynomial σ R} (hp : p ≠ 0)
    (r : MvPolynomial (Option σ) R) (hr : r ∣ projectiveHomogenize p p.totalDegree)
    (hu : IsUnit (projectiveDehomogenize r)) : IsUnit r := by
  obtain ⟨s, hs⟩ := hr
  have hH := projectiveHomogenize_ne_zero hp p.totalDegree
  have hr0 : r ≠ 0 := by
    intro h
    exact hH (by rw [hs, h, zero_mul])
  have hs0 : s ≠ 0 := by
    intro h
    exact hH (by rw [hs, h, mul_zero])
  have heq : p = projectiveDehomogenize r * projectiveDehomogenize s := by
    simpa only [projectiveDehomogenize_homogenize, map_mul] using
      congrArg (projectiveDehomogenize (R := R) (σ := σ)) hs
  have hds0 : projectiveDehomogenize s ≠ 0 := by
    intro h
    exact hp (by rw [heq, h, mul_zero])
  have hrd : (projectiveDehomogenize r).totalDegree = 0 :=
    (isUnit_iff_totalDegree_of_isReduced.mp hu).2
  have hpd : p.totalDegree = (projectiveDehomogenize s).totalDegree := by
    rw [heq, totalDegree_mul_of_isDomain hu.ne_zero hds0, hrd, zero_add]
  have hHd := projectiveHomogenize_totalDegree hp p.totalDegree le_rfl
  rw [hs, totalDegree_mul_of_isDomain hr0 hs0] at hHd
  have hb := projectiveDehomogenize_totalDegree s
  have hrdegree : r.totalDegree = 0 := by omega
  apply isUnit_iff_totalDegree_of_isReduced.mpr
  refine ⟨?_, hrdegree⟩
  apply isUnit_iff_ne_zero.mpr
  intro hc
  apply hr0
  rw [totalDegree_eq_zero_iff_eq_C.mp hrdegree, hc, map_zero]

/-- Relatively prime affine polynomials remain relatively prime after
homogenizing each to its actual degree. -/
theorem projectiveHomogenize_isRelPrime {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hcop : IsRelPrime p q) :
    IsRelPrime (projectiveHomogenize p p.totalDegree) (projectiveHomogenize q q.totalDegree) := by
  intro r hrp hrq
  have hdp : projectiveDehomogenize r ∣ p := by
    simpa only [projectiveDehomogenize_homogenize] using
      map_dvd (projectiveDehomogenize (R := R) (σ := σ)) hrp
  have hdq : projectiveDehomogenize r ∣ q := by
    simpa only [projectiveDehomogenize_homogenize] using
      map_dvd (projectiveDehomogenize (R := R) (σ := σ)) hrq
  exact homogenization_factor_isUnit hp r hrp (hcop hdp hdq)

end DimensionFourDependence
