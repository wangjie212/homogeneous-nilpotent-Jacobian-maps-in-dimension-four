import DimensionFourDependence.HomogeneousDehomogenize
import DimensionFourDependence.HomogenizeCoprime
import DimensionFourDependence.SourceDivisorMultiplicity

/-! # Lifting chart divisors to original homogeneous divisors

A divisor of the dehomogenized form homogenizes to a divisor of the
original form. Actual-degree homogenization preserves products, powers,
and irreducibility, without introducing a factor in the chart coordinate.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K σ : Type*} [Field K]

/-- Homogenization preserves a product when the two assigned degrees
bound the actual degrees of its factors. -/
theorem projectiveHomogenize_mul (p q : MvPolynomial σ K) (d e : ℕ)
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ e) :
    projectiveHomogenize (p * q) (d + e) =
      projectiveHomogenize p d * projectiveHomogenize q e := by
  apply homogeneous_dehomogenize_injective _ _
    (projectiveHomogenize_isHomogeneous _ _ ((totalDegree_mul p q).trans (Nat.add_le_add hp hq)))
    ((projectiveHomogenize_isHomogeneous p d hp).mul (projectiveHomogenize_isHomogeneous q e hq))
  rw [projectiveDehomogenize_homogenize, map_mul,
    projectiveDehomogenize_homogenize, projectiveDehomogenize_homogenize]

/-- A prime-power chart divisor homogenizes to the same power of its
actual homogeneous divisor equation. -/
theorem projectiveHomogenize_pow_actual (p : MvPolynomial σ K) (hp : p ≠ 0) (a : ℕ) :
    projectiveHomogenize (p ^ a) (a * p.totalDegree) =
      projectiveHomogenize p p.totalDegree ^ a := by
  induction a with
  | zero =>
    simp only [pow_zero, zero_mul]
    apply homogeneous_dehomogenize_injective _ _
      (projectiveHomogenize_isHomogeneous _ _ (by simp)) (isHomogeneous_one _ _)
    simp [projectiveDehomogenize_homogenize]
  | succ a ih =>
    rw [pow_succ, Nat.succ_mul,
      projectiveHomogenize_mul _ _ _ _ (totalDegree_pow_eq_of_ne_zero p hp a).le le_rfl,
      ih, pow_succ]

/-- A chart divisor lifts to a divisor of the original homogeneous form,
including zero forms and without a separate nonzero divisor assumption. -/
theorem homogenized_chart_divisor_dvd_homogeneous
    (P : MvPolynomial (Option σ) K) {d : ℕ} (hP : P.IsHomogeneous d)
    (p : MvPolynomial σ K) (hp : p ∣ projectiveDehomogenize P) :
    projectiveHomogenize p p.totalDegree ∣ P := by
  by_cases hP0 : P = 0
  · rw [hP0]
    exact dvd_zero _
  have hdP : projectiveDehomogenize P ≠ 0 := by
    intro hz
    exact hP0 (homogeneous_dehomogenize_eq_zero P hP hz)
  obtain ⟨q, hq⟩ := hp
  have hmul : p * q ≠ 0 := by rwa [← hq]
  have hdeg : p.totalDegree + q.totalDegree ≤ d := by
    rw [← totalDegree_mul_of_isDomain (left_ne_zero_of_mul hmul) (right_ne_zero_of_mul hmul), ← hq]
    exact (projectiveDehomogenize_totalDegree P).trans hP.totalDegree_le
  refine ⟨projectiveHomogenize q (d - p.totalDegree), ?_⟩
  apply homogeneous_dehomogenize_injective _ _ hP
  · have hh := (projectiveHomogenize_isHomogeneous p p.totalDegree le_rfl).mul
      (projectiveHomogenize_isHomogeneous q (d - p.totalDegree) (by omega))
    convert hh using 1
    omega
  · rw [map_mul, projectiveDehomogenize_homogenize, projectiveDehomogenize_homogenize]
    exact hq

/-- An irreducible chart divisor has an irreducible actual-degree
homogeneous equation in the original projective coordinates. -/
theorem projectiveHomogenize_irreducible (p : MvPolynomial σ K) (hp : Irreducible p) :
    Irreducible (projectiveHomogenize p p.totalDegree) := by
  constructor
  · intro hu
    apply hp.not_isUnit
    have hm := hu.map (projectiveDehomogenize (R := K) (σ := σ)).toRingHom
    change IsUnit (projectiveDehomogenize (projectiveHomogenize p p.totalDegree)) at hm
    simpa only [projectiveDehomogenize_homogenize] using hm
  · intro r s hrs
    have hd : p = projectiveDehomogenize r * projectiveDehomogenize s := by
      simpa only [projectiveDehomogenize_homogenize, map_mul] using
        congrArg (projectiveDehomogenize (R := K) (σ := σ)) hrs
    rcases hp.isUnit_or_isUnit hd with hu | hu
    · exact Or.inl (homogenization_factor_isUnit hp.ne_zero r ⟨s, hrs⟩ hu)
    · exact Or.inr (homogenization_factor_isUnit hp.ne_zero s ⟨r, by simpa [mul_comm] using hrs⟩ hu)

end DimensionFourDependence
