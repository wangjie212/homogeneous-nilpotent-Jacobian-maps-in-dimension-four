import DimensionFourDependence.DvrNormOrderBound

/-! # Arbitrary normalized functions have order bounded by their norm degree -/

namespace DimensionFourDependence

variable {k S : Type*} [Field k] [CommRing S] [IsDedekindDomain S]
  [Algebra (Polynomial k) S] [Module.Finite (Polynomial k) S] [Module.Free (Polynomial k) S]

/-- The order of any nonzero regular normalization element at a prime
above a finite base point is at most the degree of its actual norm
polynomial. The element need not be an original coordinate function. -/
theorem polynomial_normalization_local_order_le_norm_degree
    (p : Polynomial k) (hp : Irreducible p)
    (q : Ideal S) [q.IsPrime] [q.LiesOver (Ideal.span {p})]
    (z : S) (hz : z ≠ 0) (a : ℕ)
    (horder : algebraMap S (Localization.AtPrime q) z ∈
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ a) :
    a ≤ (Algebra.norm (Polynomial k) z).natDegree := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
  have hn := finite_dedekind_norm_mem_base_prime_pow (Ideal.span {p}) q z a horder
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hn
  have hd := Polynomial.natDegree_le_of_dvd hn (Algebra.norm_ne_zero_iff.mpr hz)
  rw [Polynomial.natDegree_pow] at hd
  exact (Nat.le_mul_of_pos_right a hp.natDegree_pos).trans hd

end DimensionFourDependence
