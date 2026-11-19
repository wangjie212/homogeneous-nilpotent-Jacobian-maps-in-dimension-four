import DimensionFourDependence.PolynomialScalarDenominatorDivisibility
import DimensionFourDependence.VertexIndependentReducedDenominator
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-! # A homogeneous denominator dividing a source linear power is that power

The constructed nonzero source linear polynomial is prime. Every divisor
of its power is associated to one of its powers, and homogeneity fixes
the exponent to the original denominator degree. A vertex-independent
denominator then forces the source linear polynomial itself to have
no vertex variable, constructing its actual ternary representative.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] {n : ℕ}

/-- Every nonzero homogeneous linear source polynomial over the
original field is prime. -/
theorem homogeneous_source_linear_polynomial_prime
    (Z : MvPolynomial (Fin n) K) (hZ : Z ≠ 0) (hhom : Z.IsHomogeneous 1) : Prime Z := by
  apply Irreducible.prime
  apply irreducible_of_totalDegree_eq_one (hhom.totalDegree hZ)
  obtain ⟨m, hm⟩ := support_nonempty.mpr hZ
  intro a ha
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hc := ha m
  rw [hz, zero_dvd_iff] at hc
  exact (mem_support_iff.mp hm) hc

/-- A nonzero homogeneous source denominator dividing a nonzero
linear power is a nonzero original scalar times that linear form to
exactly its homogeneous degree. -/
theorem homogeneous_denominator_dvd_linear_power_is_scalar_power
    (q Z : MvPolynomial (Fin n) K) (hq : q ≠ 0) {D d : ℕ}
    (hqhom : q.IsHomogeneous D) (hZ : Z ≠ 0) (hZhom : Z.IsHomogeneous 1)
    (hdiv : q ∣ Z ^ d) :
    D ≤ d ∧ ∃ c : K, c ≠ 0 ∧ q = C c * Z ^ D := by
  classical
  obtain ⟨e, he, hassoc⟩ := (dvd_prime_pow (homogeneous_source_linear_polynomial_prime Z hZ hZhom) d).mp hdiv
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨c, hc, hcu⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  have hqform : q = C c * Z ^ e := by
    calc
      q = Z ^ e * (u : MvPolynomial (Fin n) K) := hu.symm
      _ = C c * Z ^ e := by rw [hcu, mul_comm]
  have hqe : q.IsHomogeneous e := by
    rw [hqform]
    simpa only [one_mul] using (hZhom.pow e).C_mul c
  have heD : e = D := (hqe.totalDegree hq).symm.trans (hqhom.totalDegree hq)
  exact ⟨heD ▸ he, c, isUnit_iff_ne_zero.mp hc, by simpa only [heD] using hqform⟩

/-- A positive-degree vertex-independent homogeneous denominator
which divides a source linear power constructs an actual ternary
linear source polynomial and its exact scalar-power denominator. -/
theorem vertex_independent_denominator_linear_power_constructs_ternary_linear_form
    (q Z : MvPolynomial (Fin 4) K) (hq : q ≠ 0) {D d : ℕ} (hD : 0 < D)
    (hqhom : q.IsHomogeneous D) (hqvertex : q.degreeOf (Fin.last 3) = 0)
    (hZ : Z ≠ 0) (hZhom : Z.IsHomogeneous 1) (hdiv : q ∣ Z ^ d) :
    ∃ y : MvPolynomial (Fin 3) K, y ≠ 0 ∧ y.IsHomogeneous 1 ∧
      rename Fin.castSucc y = Z ∧ D ≤ d ∧ ∃ c : K, c ≠ 0 ∧ q = C c * (rename Fin.castSucc y) ^ D := by
  obtain ⟨hDd, c, hc, hqform⟩ := homogeneous_denominator_dvd_linear_power_is_scalar_power q Z hq hqhom hZ hZhom hdiv
  have hZvertex : Z.degreeOf (Fin.last 3) = 0 := by
    have hdeg := hqvertex
    rw [hqform, degreeOf_mul_eq (MvPolynomial.C_ne_zero.mpr hc) (pow_ne_zero D hZ),
      degreeOf_C, degreeOf_pow_eq _ _ _ hZ, zero_add] at hdeg
    exact (Nat.mul_eq_zero.mp hdeg).resolve_left (Nat.ne_of_gt hD)
  obtain ⟨y, hy⟩ := vertex_degree_zero_constructs_transverse_polynomial Z hZvertex
  have hy0 : y ≠ 0 := by intro hz; apply hZ; rw [← hy, hz, map_zero]
  have hyhom : y.IsHomogeneous 1 :=
    (IsHomogeneous.rename_isHomogeneous_iff (Fin.castSucc_injective 3)).mp (by rw [hy]; exact hZhom)
  exact ⟨y, hy0, hyhom, hy, hDd, c, hc, by simpa only [hy] using hqform⟩

end DimensionFourDependence
