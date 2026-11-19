import DimensionFourDependence.Homogeneous
import DimensionFourDependence.PrimitiveMapDegree

/-! # Divisor multiplicity in the original homogeneous common factor

A prime power dividing every component of `g P`, with `P` primitive,
already divides `g`. In a polynomial domain the resulting actual degree
bound is `a * deg(delta) ≤ deg(g)`, hence `a ≤ deg(g)` for an irreducible
source divisor. This is the polynomial conclusion of Lemma 4.2.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {σ : Type*} {n : ℕ}

/-- Prime-power common divisibility of a polynomial vector is entirely
carried by its common scalar factor after taking a primitive part. -/
theorem prime_power_dvd_common_factor_of_primitive
    (P : Fin n → MvPolynomial σ K) (hP : IsPrimitiveVec P)
    (δ : MvPolynomial σ K) (hδ : Prime δ) (a : ℕ)
    (g : MvPolynomial σ K) (hdiv : ∀ i, δ ^ a ∣ g * P i) : δ ^ a ∣ g := by
  induction a generalizing g with
  | zero => simp
  | succ a ih =>
    have hδg : δ ∣ g := by
      by_contra hn
      apply hδ.not_isUnit
      apply hP δ
      intro i
      have hd : δ ∣ g * P i := (show δ ∣ δ ^ (a + 1) from ⟨δ ^ a, pow_succ' δ a⟩).trans (hdiv i)
      exact (hδ.dvd_mul.mp hd).resolve_left hn
    obtain ⟨g₁, rfl⟩ := hδg
    have hdiv₁ : ∀ i, δ ^ a ∣ g₁ * P i := by
      intro i
      have hh : δ * δ ^ a ∣ δ * (g₁ * P i) := by
        simpa only [pow_succ', mul_assoc] using hdiv i
      exact (mul_dvd_mul_iff_left hδ.ne_zero).mp hh
    obtain ⟨r, hr⟩ := ih g₁ hdiv₁
    exact ⟨r, by rw [hr, pow_succ', mul_assoc]⟩

/-- Powers have their actual additive total degree over a polynomial domain. -/
theorem totalDegree_pow_eq_of_ne_zero (δ : MvPolynomial σ K) (hδ : δ ≠ 0) (a : ℕ) :
    (δ ^ a).totalDegree = a * δ.totalDegree := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, totalDegree_mul_of_isDomain (pow_ne_zero a hδ) hδ, ih]
    simp only [Nat.add_mul, one_mul]

/-- A nonzero polynomial prime has positive actual source degree. -/
theorem prime_polynomial_totalDegree_pos (δ : MvPolynomial σ K) (hδ : Prime δ) :
    0 < δ.totalDegree := by
  by_contra hn
  have hd0 : δ.totalDegree = 0 := by omega
  apply hδ.not_isUnit
  apply isUnit_iff_totalDegree_of_isReduced.mpr
  refine ⟨?_, hd0⟩
  apply isUnit_iff_ne_zero.mpr
  intro hc
  exact hδ.ne_zero (by rw [totalDegree_eq_zero_iff_eq_C.mp hd0, hc, map_zero])

/-- An order lower bound on every original component forces the precise
degree lower bound on the actual common factor. -/
theorem source_divisor_multiplicity_common_factor_degree
    (H P : Fin n → MvPolynomial σ K) (g : MvPolynomial σ K)
    (hg : g ≠ 0) (hP : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (δ : MvPolynomial σ K) (hδ : Irreducible δ) (a : ℕ)
    (hdiv : ∀ i, δ ^ a ∣ H i) :
    δ ^ a ∣ g ∧ a * δ.totalDegree ≤ g.totalDegree ∧ a ≤ g.totalDegree := by
  have hδp : Prime δ := irreducible_iff_prime.mp hδ
  have hd : δ ^ a ∣ g := prime_power_dvd_common_factor_of_primitive P hP δ hδp a g
    (fun i => by rw [← congrFun hHP i]; exact hdiv i)
  have hdeg := totalDegree_le_of_dvd_of_isDomain hd hg
  rw [totalDegree_pow_eq_of_ne_zero δ hδp.ne_zero a] at hdeg
  have hpos := prime_polynomial_totalDegree_pos δ hδp
  exact ⟨hd, hdeg, (Nat.le_mul_of_pos_right a hpos).trans hdeg⟩

end DimensionFourDependence
