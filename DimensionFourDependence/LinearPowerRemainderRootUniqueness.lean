import DimensionFourDependence.PowerRemainderUniqueness
import DimensionFourDependence.PrimitiveLinearIncidence
import DimensionFourDependence.ModifiedCubicFiberBoundary

/-! # The root of multiplicity nonzero modulo d is intrinsic to a linear-times-power form -/

namespace DimensionFourDependence

open MvPolynomial UniqueFactorizationMonoid

set_option maxHeartbeats 2500000

/-- An irreducible has each actual normalized prime multiplicity at most one. -/
theorem irreducible_actual_factorization_le_one
    {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] [DecidableEq R] (A : R) (hA : Irreducible A) (p : R) :
    factorization A p ≤ 1 := by
  rw [factorization_eq_count, normalizedFactors_irreducible hA, Multiset.count_singleton]
  split_ifs <;> omega

/-- Two irreducible-times-dth-power presentations have the same
irreducible remainder up to a unit when d>1, even for coincident factors. -/
theorem irreducible_times_power_remainders_associated
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (A B C D : R) (hA : Irreducible A) (hC : Irreducible C)
    (hB : B ≠ 0) (hD : D ≠ 0) (d : ℕ) (hd : 1 < d)
    (he : A * B ^ d = C * D ^ d) : Associated A C := by
  classical
  letI : NormalizedGCDMonoid R := Classical.arbitrary (NormalizedGCDMonoid R)
  have hP : A * B ^ d ≠ 0 := mul_ne_zero hA.ne_zero (pow_ne_zero d hB)
  have ha (p : R) : factorization A p < d :=
    (irreducible_actual_factorization_le_one A hA p).trans_lt hd
  have hc (p : R) : factorization C p < d :=
    (irreducible_actual_factorization_le_one C hC p).trans_lt hd
  have hfirst := (actual_power_remainder_quotient_unique (A * B ^ d) A B d (by omega)
    hP hA.ne_zero hB (Associated.refl _) ha).1
  have hsecond := (actual_power_remainder_quotient_unique (A * B ^ d) C D d (by omega)
    hP hC.ne_zero hD (Associated.of_eq he) hc).1
  exact hfirst.symm.trans hsecond

/-- A nonzero linear form over a field is an actual irreducible polynomial. -/
theorem nonzero_linear_form_irreducible
    {K : Type*} [Field K] {n : ℕ} (a : Fin n → K) (ha : a ≠ 0) :
    Irreducible (linearFormPolynomial a) := by
  apply coefficientLinearForm_irreducible a ha
  intro r hr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  apply ha
  funext i
  exact zero_dvd_iff.mp (by simpa only [hz] using hr i)

/-- The distinguished remainder root is retained after any specified
field embedding and for any actual representing vector. -/
theorem linear_times_power_remainder_root_preserved
    {K F : Type*} [Field K] [Field F] {n : ℕ}
    (φ : K →+* F) (a b c e : Fin n → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he0 : e ≠ 0)
    (d : ℕ) (hd : 1 < d)
    (hpower : linearFormPolynomial a * linearFormPolynomial b ^ d =
      linearFormPolynomial c * linearFormPolynomial e ^ d)
    (w : Fin n → F) (hroot : MvPolynomial.eval₂ φ w (linearFormPolynomial a) = 0) :
    MvPolynomial.eval₂ φ w (linearFormPolynomial c) = 0 := by
  have hB : linearFormPolynomial b ≠ 0 := coefficientLinearForm_ne_zero b hb
  have hE : linearFormPolynomial e ≠ 0 := coefficientLinearForm_ne_zero e he0
  have hassoc := irreducible_times_power_remainders_associated
    _ _ _ _ (nonzero_linear_form_irreducible a ha) (nonzero_linear_form_irreducible c hc)
    hB hE d hd hpower
  obtain ⟨Q, hQ⟩ := hassoc.dvd
  rw [hQ, MvPolynomial.eval₂_mul, hroot, zero_mul]

end DimensionFourDependence
