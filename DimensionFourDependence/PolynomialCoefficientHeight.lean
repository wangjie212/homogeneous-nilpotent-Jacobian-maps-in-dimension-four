import DimensionFourDependence.ImageEquationWitness

/-! # Height bound from independent polynomial coefficients

A prime of `R[t]` containing no nonzero coefficient has height at most
one. Localize the coefficients to their fraction field, preserve the
prime height, and use that a polynomial ring over a field has dimension one.
-/

namespace DimensionFourDependence

variable {R : Type*} [CommRing R] [IsDomain R]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

/-- A polynomial prime over zero in the coefficient domain has height at most one. -/
theorem polynomial_prime_height_le_one_of_coefficient_comap
    (P : Ideal (Polynomial R)) [P.IsPrime]
    (hcoeff : P.comap Polynomial.C = ⊥) : P.height ≤ 1 := by
  let M : Submonoid (Polynomial R) := (nonZeroDivisors R).map Polynomial.C
  have hdisj : Disjoint (M : Set (Polynomial R)) (P : Set (Polynomial R)) := by
    apply Set.disjoint_left.mpr
    intro p hp hpP
    obtain ⟨r, hr, rfl⟩ := hp
    have hz : r ∈ P.comap Polynomial.C := hpP
    rw [hcoeff, Ideal.mem_bot] at hz
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) hz
  let Q := P.map (algebraMap (Polynomial R) (Polynomial (FractionRing R)))
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M
    (Polynomial (FractionRing R)) P inferInstance hdisj
  have he : Q.height = P.height := IsLocalization.height_map_of_disjoint M P hdisj
  rw [← he]
  apply WithBot.coe_le_coe.mp
  simpa using (Ideal.height_le_ringKrullDim_of_ne_top (I := Q) Ideal.IsPrime.ne_top')

end DimensionFourDependence
