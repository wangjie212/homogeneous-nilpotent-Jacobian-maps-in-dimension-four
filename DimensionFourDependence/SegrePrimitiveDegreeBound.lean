import DimensionFourDependence.SourceDivisorMultiplicity
import DimensionFourDependence.StandardRulingQuadric

/-! # The original primitive map supplies the Segre common-order degree bound -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

/-- A determinant power in the actual homogeneous common factor has
order strictly below half the original degree whenever the primitive
map has degree at least two. -/
theorem segre_determinant_power_common_factor_degree_bound
    (g : MvPolynomial (Fin 4) K) {c d : ℕ} (hg : g ≠ 0) (hgh : g.IsHomogeneous c)
    (hdegree : 2 ≤ d - c) (j : ℕ) (hdiv : standardRulingPolynomial (F := K) ^ j ∣ g) :
    2 * j < d := by
  have hdeg := totalDegree_le_of_dvd_of_isDomain hdiv hg
  rw [totalDegree_pow_eq_of_ne_zero _ (standardRulingPolynomial_ne_zero (F := K)) j,
    (standardRulingPolynomial_homogeneous (F := K)).totalDegree (standardRulingPolynomial_ne_zero (F := K)),
    hgh.totalDegree hg] at hdeg
  omega

/-- The original independent homogeneous map and its actual image
relation construct a primitive common factor for which every actual
determinant-power divisor satisfies the degree inequality needed by
Lemma 5.2. No primitive degree or numeric order bound is supplied. -/
theorem original_map_constructs_segre_primitive_order_degree_bound
    [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (hind : ¬ComponentsDependent H) (I : ImageRelationWitness H) :
    ∃ (g : MvPolynomial (Fin 4) K) (P : Fin 4 → MvPolynomial (Fin 4) K) (c : ℕ),
      g ≠ 0 ∧ g.IsHomogeneous c ∧ IsHomogMap P (d - c) ∧ IsPrimitiveVec P ∧
      H = (fun i => g * P i) ∧
      ∀ j : ℕ, standardRulingPolynomial (F := K) ^ j ∣ g → 2 * j < d := by
  obtain ⟨g, P, c, _hc, hg, hgh, hP, hprim, hHP, hdegree⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  exact ⟨g, P, c, hg, hgh, hP, hprim, hHP,
    fun j hdiv => segre_determinant_power_common_factor_degree_bound g hg hgh hdegree j hdiv⟩

end DimensionFourDependence
