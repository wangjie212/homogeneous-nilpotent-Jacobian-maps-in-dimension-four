import DimensionFourDependence.NilpotentPencilMinorDivisibility

/-! # A simple source zero constructs the actual prime pencil factor and its tangent equation -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] {n : ℕ}
local notation "P₀" => MvPolynomial (Fin n) K

/-- The actual prime kernel of point evaluation selects a prime
factor through that point from the finite irreducible factorization. -/
theorem nonzero_polynomial_zero_constructs_prime_divisor_vanishing_at_point
    (p : P₀) (hp : p ≠ 0) (z : Fin n → K) (hpz : aeval z p = 0) :
    ∃ δ : P₀, Prime δ ∧ δ ∣ p ∧ aeval z δ = 0 := by
  classical
  let I : Ideal P₀ := RingHom.ker (aeval z : P₀ →ₐ[K] K)
  letI : I.IsPrime := RingHom.ker_isPrime _
  have hpI : p ∈ I := hpz
  obtain ⟨s, hs, hassoc⟩ := WfDvdMonoid.exists_factors p hp
  have hprodI : s.prod ∈ I := by
    obtain ⟨b, hb⟩ := hassoc.symm.dvd
    rw [hb]
    exact I.mul_mem_right b hpI
  obtain ⟨δ, hδs, hδI⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem
    (inferInstance : I.IsPrime) s).mp hprodI
  exact ⟨δ, UniqueFactorizationMonoid.irreducible_iff_prime.mp (hs δ hδs),
    (Multiset.dvd_prod hδs).trans hassoc.dvd, hδI⟩

/-- A nonzero source derivative makes the selected prime factor
simple at the original point and transfers the actual numerator minor
to that prime factor. Its relative primality and nondivisibility of
the active output are derived at the same original point. -/
theorem simple_source_pencil_zero_constructs_homogeneous_prime_factor_with_tangent_minor
    (p q F : P₀) {D : ℕ} (hpH : p.IsHomogeneous D) (hrel : IsRelPrime p q)
    (z : Fin n → K) (j k : Fin n) (hpz : aeval z p = 0)
    (hpder : aeval z (pderiv j p) ≠ 0) (hFz : aeval z F ≠ 0)
    (hminor : p ∣ sourceJacobianMinor F p j k) :
    ∃ (δ b : P₀) (e : ℕ), Prime δ ∧ 0 < e ∧ δ.IsHomogeneous e ∧
      p = δ * b ∧ IsRelPrime δ q ∧ aeval z δ = 0 ∧ aeval z b ≠ 0 ∧
      aeval z (pderiv j δ) ≠ 0 ∧ ¬δ ∣ F ∧ δ ∣ sourceJacobianMinor F δ j k := by
  have hp : p ≠ 0 := by intro hz; simp only [hz, map_zero] at hpder; exact hpder rfl
  obtain ⟨δ, hδ, hδp, hδz⟩ := nonzero_polynomial_zero_constructs_prime_divisor_vanishing_at_point p hp z hpz
  obtain ⟨b, hb⟩ := hδp
  obtain ⟨e, hδH⟩ := isHomogeneous_of_mul_left (hb ▸ hpH) (by rw [← hb]; exact hp)
  have he : 0 < e := by
    by_contra hn
    have he0 : e = 0 := by omega
    exact hδ.not_isUnit (isUnit_of_isHomogeneous_zero (he0 ▸ hδH) hδ.ne_zero)
  have hvalue : aeval z (pderiv j p) = aeval z (pderiv j δ) * aeval z b := by
    rw [hb, pderiv_mul, map_add, map_mul, map_mul, hδz, zero_mul, add_zero]
  have hmulne : aeval z (pderiv j δ) * aeval z b ≠ 0 := hvalue ▸ hpder
  have hδder := (mul_ne_zero_iff.mp hmulne).1
  have hbz := (mul_ne_zero_iff.mp hmulne).2
  have hδb : ¬δ ∣ b := by
    rintro ⟨c, hc⟩
    apply hbz
    rw [hc, map_mul, hδz, zero_mul]
  have hδF : ¬δ ∣ F := by
    rintro ⟨c, hc⟩
    apply hFz
    rw [hc, map_mul, hδz, zero_mul]
  have hδminor : δ ∣ sourceJacobianMinor F p j k := (show δ ∣ p from ⟨b, hb⟩).trans hminor
  have hprod : sourceJacobianMinor F p j k =
      b * sourceJacobianMinor F δ j k + δ * sourceJacobianMinor F b j k := by
    rw [hb]
    simp only [sourceJacobianMinor, pderiv_mul]
    ring
  rw [hprod] at hδminor
  have hδprod : δ ∣ b * sourceJacobianMinor F δ j k := by
    have h := dvd_sub hδminor (dvd_mul_right δ (sourceJacobianMinor F b j k))
    simpa only [add_sub_cancel_right] using h
  have htangent : δ ∣ sourceJacobianMinor F δ j k := (hδ.dvd_mul.mp hδprod).resolve_left hδb
  exact ⟨δ, b, e, hδ, he, hδH, hb, hrel.of_dvd_left ⟨b, hb⟩,
    hδz, hbz, hδder, hδF, htangent⟩

end DimensionFourDependence
