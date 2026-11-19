import DimensionFourDependence.VertexPolynomialCoefficientClearing

/-! # A reduced polynomial vertex parameter has transverse denominator

A polynomial value in K(x_1,x_2,x_3)[w] has an actual ternary common
denominator. For an original reduced source quotient p/q, coprimality
then forces q to divide that ternary polynomial. Additivity of the
vertex degree makes q independent of w, and variable elimination
constructs its actual ternary polynomial representative.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K]

local notation "A₀" => MvPolynomial (Fin 3) K
local notation "R₀" => MvPolynomial (Fin 4) K
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "L₀" => transverseSourceField K
local notation "w₀" => rationalCoordinate (K := K) (Fin.last 3)

/-- Vertex degree zero constructs an actual ternary source polynomial,
not merely a rational expression independent of the vertex. -/
theorem vertex_degree_zero_constructs_transverse_polynomial (q : R₀)
    (hq : q.degreeOf (Fin.last 3) = 0) :
    ∃ q₀ : A₀, rename Fin.castSucc q₀ = q := by
  classical
  apply exists_rename_eq_of_vars_subset_range q Fin.castSucc (Fin.castSucc_injective 3)
  intro i hi
  have hne : i ≠ Fin.last 3 := by
    intro heq
    subst i
    exact (mem_vars_iff_degreeOf_ne_zero.mp hi) hq
  exact Fin.eq_castSucc_of_ne_last hne

variable [CharZero K]

/-- If an original reduced quotient has a polynomial vertex value,
its entire original denominator has vertex degree zero. The common
ternary denominator is constructed from the actual coefficient field. -/
theorem reduced_source_quotient_polynomial_vertex_denominator_degree_zero
    (p q : R₀) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (U : Polynomial L₀)
    (hvalue : Polynomial.aeval w₀ U = algebraMap R₀ S₀ p / algebraMap R₀ S₀ q) :
    q.degreeOf (Fin.last 3) = 0 := by
  obtain ⟨c, hc, V, hV⟩ := vertex_polynomial_value_clears_transverse_source_denominator U
  have hqS : algebraMap R₀ S₀ q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R₀ S₀).ne hq
  rw [hvalue] at hV
  have hcross : rename Fin.castSucc c * p = q * V := by
    apply IsFractionRing.injective R₀ S₀
    simp only [map_mul]
    have hh := congrArg (fun z : S₀ => z * algebraMap R₀ S₀ q) hV
    rw [mul_assoc, div_mul_cancel₀ _ hqS] at hh
    exact hh.trans (mul_comm _ _)
  have hdiv : q ∣ rename Fin.castSucc c := hrel.symm.dvd_of_dvd_mul_left
    (show q ∣ p * rename Fin.castSucc c from ⟨V, by rw [mul_comm p]; exact hcross⟩)
  have hcR : rename Fin.castSucc c ≠ (0 : R₀) := by
    simpa only [map_zero] using (rename_injective Fin.castSucc (Fin.castSucc_injective 3)).ne hc
  obtain ⟨s, hs⟩ := hdiv
  have hs0 : s ≠ 0 := by intro h; rw [h, mul_zero] at hs; exact hcR hs
  have hdeg := transverse_rename_vertex_degree_zero c
  rw [hs, degreeOf_mul_eq hq hs0] at hdeg
  omega

/-- Coprimality and polynomiality in the original vertex construct
q=q(x) as a nonzero actual ternary source polynomial. -/
theorem reduced_source_quotient_polynomial_vertex_denominator_is_ternary
    (p q : R₀) (hq : q ≠ 0) (hrel : IsRelPrime p q)
    (U : Polynomial L₀)
    (hvalue : Polynomial.aeval w₀ U = algebraMap R₀ S₀ p / algebraMap R₀ S₀ q) :
    ∃ q₀ : A₀, q₀ ≠ 0 ∧ rename Fin.castSucc q₀ = q := by
  obtain ⟨q₀, hq₀⟩ := vertex_degree_zero_constructs_transverse_polynomial q
    (reduced_source_quotient_polynomial_vertex_denominator_degree_zero p q hq hrel U hvalue)
  refine ⟨q₀, ?_, hq₀⟩
  intro hz
  apply hq
  rw [← hq₀, hz, map_zero]

end DimensionFourDependence
