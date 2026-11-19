import DimensionFourDependence.Defs

/-! # Affine polynomial substitution does not increase total degree -/

namespace DimensionFourDependence

open MvPolynomial

variable {k σ τ : Type*} [Field k]

/-- Replacing every variable by a polynomial of total degree at most
one never increases total degree, including when leading terms cancel. -/
theorem totalDegree_aeval_le_of_affine
    (g : σ → MvPolynomial τ k) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (f : MvPolynomial σ k) : (aeval g f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [aeval_monomial]
  have hprod : (d.prod (fun i n => g i ^ n)).totalDegree ≤ d.sum (fun _ n => n) := by
    apply (totalDegree_finsetProd d.support (fun i => g i ^ d i)).trans
    apply Finset.sum_le_sum
    intro i _
    exact (totalDegree_pow (g i) (d i)).trans (by simpa using Nat.mul_le_mul_left (d i) (hg i))
  exact (totalDegree_mul _ _).trans (by
    simpa only [algebraMap_eq, totalDegree_C, zero_add] using hprod.trans (le_totalDegree hd))

end DimensionFourDependence
