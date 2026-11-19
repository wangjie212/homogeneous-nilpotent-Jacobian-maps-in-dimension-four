import DimensionFourDependence.Defs

/-! # A derivation fixing a principal equation descends to its actual quotient -/

namespace DimensionFourDependence

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

/-- Killing the principal equation preserves its entire quotient
kernel, by the original product rule. -/
theorem principal_equation_derivation_preserves_quotient_kernel
    (D : Derivation K R R) (p : R) (hDp : D p = 0)
    (r : R) (hr : Ideal.Quotient.mk (Ideal.span {p}) r = 0) :
    Ideal.Quotient.mk (Ideal.span {p}) (D r) = 0 := by
  let I : Ideal R := Ideal.span {p}
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hr)
  have hp : Ideal.Quotient.mk I p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton p))
  rw [hb, D.leibniz, hDp]
  simp only [smul_eq_mul, mul_zero, add_zero, map_mul]
  change Ideal.Quotient.mk I p * Ideal.Quotient.mk I (D b) = 0
  rw [hp, zero_mul]

/-- The actual quotient derivation, with no assumed differential
structure on the hypersurface ring. -/
noncomputable def principalQuotientDerivation
    (D : Derivation K R R) (p : R) (hDp : D p = 0) :
    Derivation K (R ⧸ Ideal.span {p}) (R ⧸ Ideal.span {p}) :=
  Derivation.liftOfSurjective (f := Ideal.Quotient.mkₐ K (Ideal.span {p}))
    Ideal.Quotient.mk_surjective (principal_equation_derivation_preserves_quotient_kernel D p hDp)

/-- Every original polynomial retains its exact derivative after
passing to the principal quotient. -/
theorem principalQuotientDerivation_mk
    (D : Derivation K R R) (p : R) (hDp : D p = 0) (r : R) :
    principalQuotientDerivation D p hDp (Ideal.Quotient.mk (Ideal.span {p}) r) =
      Ideal.Quotient.mk (Ideal.span {p}) (D r) :=
  Derivation.liftOfSurjective_apply (f := Ideal.Quotient.mkₐ K (Ideal.span {p}))
    Ideal.Quotient.mk_surjective (principal_equation_derivation_preserves_quotient_kernel D p hDp) r

end DimensionFourDependence
