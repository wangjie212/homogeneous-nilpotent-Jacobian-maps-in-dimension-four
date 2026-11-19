import DimensionFourDependence.Defs

/-! # Denominator ideals in the specified fraction field

The ideal of multipliers making a rational function regular detects its
regularity at a prime. Noetherianity constructs a prime denominator
ideal containing the denominator ideal of a given nonregular fraction.
-/

namespace DimensionFourDependence

variable (R : Type*) {F : Type*} [CommRing R] [Field F] [Algebra R F]

/-- Multipliers in the original ring which make the specified
fraction an element of that ring. -/
def fractionDenominatorIdeal (x : F) : Ideal R where
  carrier := {a | IsLocalization.IsInteger R (algebraMap R F a * x)}
  zero_mem' := by simpa using (IsLocalization.isInteger_zero (R := R) (S := F))
  add_mem' := by
    intro a b ha hb
    change IsLocalization.IsInteger R (algebraMap R F (a + b) * x)
    rw [map_add, add_mul]
    exact IsLocalization.isInteger_add ha hb
  smul_mem' := by
    intro a b hb
    change IsLocalization.IsInteger R (algebraMap R F (a * b) * x)
    rw [map_mul, mul_assoc]
    exact IsLocalization.isInteger_mul ⟨a, rfl⟩ hb

/-- Membership retains the actual multiplier and fraction. -/
theorem mem_fractionDenominatorIdeal (x : F) (a : R) :
    a ∈ fractionDenominatorIdeal R x ↔
      ∃ b : R, algebraMap R F b = algebraMap R F a * x := Iff.rfl

/-- A fraction is regular precisely when its denominator ideal is
the whole original ring. -/
theorem fractionDenominatorIdeal_eq_top_iff (x : F) :
    fractionDenominatorIdeal R x = ⊤ ↔ IsLocalization.IsInteger R x := by
  rw [Ideal.eq_top_iff_one, mem_fractionDenominatorIdeal]
  simp only [map_one, one_mul]
  rfl

/-- Multiplication by an original-ring element can only enlarge
the denominator ideal. -/
theorem fractionDenominatorIdeal_le_mul (x : F) (a : R) :
    fractionDenominatorIdeal R x ≤ fractionDenominatorIdeal R (algebraMap R F a * x) := by
  intro b hb
  obtain ⟨c, hc⟩ := (mem_fractionDenominatorIdeal R x b).mp hb
  apply (mem_fractionDenominatorIdeal R _ b).mpr
  refine ⟨a * c, ?_⟩
  rw [map_mul, hc]
  ring

variable [IsDomain R] [IsFractionRing R F]

/-- Every actual fraction has a nonzero original-ring denominator. -/
theorem fractionDenominatorIdeal_ne_bot (x : F) : fractionDenominatorIdeal R x ≠ ⊥ := by
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective R x
  have hmem : b ∈ fractionDenominatorIdeal R x := by
    apply (mem_fractionDenominatorIdeal R x b).mpr
    refine ⟨a, ?_⟩
    rw [← hx]
    have hb0 : algebraMap R F b ≠ 0 :=
      by simpa only [map_zero] using
        (IsFractionRing.injective R F).ne (mem_nonZeroDivisors_iff_ne_zero.mp hb)
    field_simp [hb0]
  intro he
  rw [he, Ideal.mem_bot] at hmem
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hb) hmem

variable [IsNoetherianRing R]

/-- A nonregular fraction admits a prime denominator ideal containing
its own denominator ideal. The witnessing fraction remains nonregular.
This uses the ascending chain condition on actual denominator ideals. -/
theorem nonregular_fraction_constructs_prime_denominator
    (x : F) (hx : ¬IsLocalization.IsInteger R x) :
    ∃ (y : F) (P : Ideal R), P.IsPrime ∧
      ¬IsLocalization.IsInteger R y ∧ P = fractionDenominatorIdeal R y ∧
      fractionDenominatorIdeal R x ≤ P := by
  obtain ⟨P, ⟨hle, y, hy, hP⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherianRing R)
      {P : Ideal R | fractionDenominatorIdeal R x ≤ P ∧
        ∃ y : F, ¬IsLocalization.IsInteger R y ∧ P = fractionDenominatorIdeal R y}
      ⟨fractionDenominatorIdeal R x, le_rfl, x, hx, rfl⟩
  have hprime : Ideal.IsPrime P := by
    rw [hP]
    refine ⟨?_, ?_⟩
    · exact fun he => hy ((fractionDenominatorIdeal_eq_top_iff R y).mp he)
    · intro a b hab
      rw [or_iff_not_imp_left]
      intro ha
      have hay : ¬IsLocalization.IsInteger R (algebraMap R F a * y) := ha
      have hle' := fractionDenominatorIdeal_le_mul R y a
      have he : fractionDenominatorIdeal R (algebraMap R F a * y) = P := by
        have hleP : P ≤ fractionDenominatorIdeal R (algebraMap R F a * y) := hP ▸ hle'
        exact (hleP.eq_of_not_lt (hmax _
          ⟨hle.trans hleP, algebraMap R F a * y, hay, rfl⟩)).symm
      rw [← hP, ← he]
      obtain ⟨c, hc⟩ := (mem_fractionDenominatorIdeal R y (a * b)).mp hab
      apply (mem_fractionDenominatorIdeal R _ b).mpr
      refine ⟨c, ?_⟩
      rw [hc, map_mul]
      ring
  exact ⟨y, P, hprime, hy, hP, hle⟩

end DimensionFourDependence
