import DimensionFourDependence.ProjectiveComponents

/-! # Relations between two relatively prime equations

The two-term Koszul relation generates every syzygy. The homogeneous
version controls its degree, as required for the intersection Hilbert function.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

omit [IsDomain R] in
/-- Relative primality makes the second equation a non-zero-divisor
modulo the first principal ideal. -/
theorem relPrime_mul_mem_principal_iff (p q a : R) (hcop : IsRelPrime p q) :
    q * a ∈ Ideal.span ({p} : Set R) ↔ a ∈ Ideal.span ({p} : Set R) := by
  simp only [Ideal.mem_span_singleton]
  exact ⟨hcop.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h q⟩

omit [IsDomain R] in
/-- Relatively prime principal ideals meet in their product. -/
theorem relPrime_principal_inf (p q : R) (hcop : IsRelPrime p q) :
    Ideal.span ({p} : Set R) ⊓ Ideal.span ({q} : Set R) = Ideal.span ({p * q} : Set R) := by
  ext a
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton]
  exact ⟨fun h => hcop.mul_dvd h.1 h.2, fun h => ⟨dvd_of_mul_right_dvd h, dvd_of_mul_left_dvd h⟩⟩

/-- Every relation on a relatively prime pair is a multiple of `(q,-p)`. -/
theorem relPrime_pair_syzygy (p q : R) (hp : p ≠ 0) (hcop : IsRelPrime p q)
    (a b : R) (hrel : p * a + q * b = 0) : ∃ c, a = q * c ∧ b = -p * c := by
  have hd : p ∣ q * b := ⟨-a, by linear_combination hrel⟩
  obtain ⟨c, rfl⟩ := hcop.dvd_of_dvd_mul_left hd
  have ha : a = -q * c := by
    apply mul_left_cancel₀ hp
    linear_combination hrel
  exact ⟨-c, by rw [ha]; ring, by ring⟩

/-- The relation map in the two-equation Koszul complex. -/
noncomputable def completeIntersectionRelationMap (p q : R) : R →ₗ[R] R × R where
  toFun c := (q * c, -p * c)
  map_add' a b := by ext <;> simp [mul_add]
  map_smul' a b := by ext <;> simp [smul_eq_mul, mul_left_comm]

/-- The map taking coefficients to a combination of the two equations. -/
noncomputable def completeIntersectionEquationMap (p q : R) : R × R →ₗ[R] R where
  toFun z := p * z.1 + q * z.2
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, mul_add]; ring
  map_smul' a b := by simp [smul_eq_mul]; ring

omit [UniqueFactorizationMonoid R] in
theorem completeIntersectionRelationMap_injective (p q : R) (hp : p ≠ 0) :
    Function.Injective (completeIntersectionRelationMap p q) := by
  intro a b hab
  exact mul_left_cancel₀ (neg_ne_zero.mpr hp) (congrArg Prod.snd hab)

/-- Exactness of the pair's Koszul complex at the relation module. -/
theorem completeIntersection_pair_exact (p q : R) (hp : p ≠ 0) (hcop : IsRelPrime p q) :
    LinearMap.range (completeIntersectionRelationMap p q) =
      LinearMap.ker (completeIntersectionEquationMap p q) := by
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    change p * (q * c) + q * (-p * c) = 0
    ring
  · intro hz
    change p * z.1 + q * z.2 = 0 at hz
    obtain ⟨c, ha, hb⟩ := relPrime_pair_syzygy p q hp hcop z.1 z.2 hz
    exact ⟨c, Prod.ext ha.symm hb.symm⟩

variable {L σ : Type*} [Field L]

/-- Cancelling a nonzero homogeneous factor preserves the prescribed
degree of the other factor, including when that other factor is zero. -/
theorem homogeneous_factor_of_product {p c : MvPolynomial σ L} {d m : ℕ}
    (hp0 : p ≠ 0) (hp : p.IsHomogeneous d) (hpc : (p * c).IsHomogeneous (d + m)) :
    c.IsHomogeneous m := by
  have he := homogeneousComponent_mul_of_isHomogeneous hp c m
  rw [Nat.add_comm m d, homogeneousComponent_of_mem hpc, ite_eq_left rfl] at he
  have hc : c = homogeneousComponent m c := mul_left_cancel₀ hp0 he
  rw [hc]
  exact homogeneousComponent_isHomogeneous m c

/-- The multiplier of a homogeneous relation has the expected degree. -/
theorem relPrime_pair_homogeneous_syzygy
    (p q : MvPolynomial σ L) {d m : ℕ} (hp0 : p ≠ 0) (hp : p.IsHomogeneous d)
    (hcop : IsRelPrime p q) (a b : MvPolynomial σ L)
    (hb : b.IsHomogeneous (d + m)) (hrel : p * a + q * b = 0) :
    ∃ c : MvPolynomial σ L, c.IsHomogeneous m ∧ a = q * c ∧ b = -p * c := by
  obtain ⟨c, ha, he⟩ := relPrime_pair_syzygy p q hp0 hcop a b hrel
  have hpc : (p * c).IsHomogeneous (d + m) := by
    have he' : p * c = -b := by rw [he]; ring
    rw [he']
    exact hb.neg
  exact ⟨c, homogeneous_factor_of_product hp0 hp hpc, ha, he⟩

end DimensionFourDependence
