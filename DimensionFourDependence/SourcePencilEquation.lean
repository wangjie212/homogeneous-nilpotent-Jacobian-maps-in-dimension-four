import DimensionFourDependence.HomogeneousGaussParameter

/-! # The exact independent-parameter equation of a rational source pencil

For a reduced quotient `p/q`, the polynomial `p - T q` is primitive and
irreducible over the source polynomial ring. Gauss's lemma and the factor
theorem identify the whole kernel of evaluation at `T = p/q` with this
single equation. This constructs the independent-parameter pencil equation
for the actual homogeneous Gauss parameter.
-/

namespace DimensionFourDependence

section Pencil

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The independent-parameter equation `p - T q` of a source pencil. -/
noncomputable def sourcePencilEquation (p q : R) : Polynomial R :=
  Polynomial.C (-q) * Polynomial.X + Polynomial.C p

omit [IsDomain R] in
/-- Relatively prime numerator and denominator make the actual pencil
equation primitive over its source coefficient ring. -/
theorem sourcePencilEquation_isPrimitive (p q : R) (hrel : IsRelPrime p q) :
    (sourcePencilEquation p q).IsPrimitive := by
  intro r hr
  have hc := (Polynomial.C_dvd_iff_dvd_coeff r (sourcePencilEquation p q)).mp hr
  apply hrel
  · simpa [sourcePencilEquation] using hc 0
  · have hh : r ∣ -q := by simpa [sourcePencilEquation] using hc 1
    exact dvd_neg.mp hh

/-- The genuine source pencil equation is irreducible in the
independent parameter, with no algebraic-closedness hypothesis. -/
theorem sourcePencilEquation_irreducible
    (p q : R) (hq : q ≠ 0) (hrel : IsRelPrime p q) : Irreducible (sourcePencilEquation p q) := by
  apply Polynomial.irreducible_C_mul_X_add_C (neg_ne_zero.mpr hq)
  intro r hrq hrp
  exact hrel hrp (dvd_neg.mp hrq)

/-- Substitution of the actual quotient annihilates its independent
parameter equation in the actual source fraction field. -/
theorem sourcePencilEquation_eval_fraction (p q : R) (hq : q ≠ 0) :
    Polynomial.eval₂ (algebraMap R (FractionRing R))
      (algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q)
      (sourcePencilEquation p q) = 0 := by
  have hqF : algebraMap R (FractionRing R) q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R (FractionRing R)).ne hq
  simp only [sourcePencilEquation, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_neg, map_neg]
  field_simp [hqF]
  ring

/-- After passing to the source fraction field, the pencil equation
is a nonzero constant multiple of the linear factor of its actual root. -/
theorem sourcePencilEquation_map_fraction_factor (p q : R) (hq : q ≠ 0) :
    Polynomial.map (algebraMap R (FractionRing R)) (sourcePencilEquation p q) =
      Polynomial.C (-algebraMap R (FractionRing R) q) *
        (Polynomial.X - Polynomial.C
          (algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q)) := by
  have hqF : algebraMap R (FractionRing R) q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R (FractionRing R)).ne hq
  have he : (-algebraMap R (FractionRing R) q) *
      (algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q) =
        -algebraMap R (FractionRing R) p := by field_simp
  simp only [sourcePencilEquation, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_neg, map_neg]
  have hh := congrArg (Polynomial.C : FractionRing R →+* Polynomial (FractionRing R)) he
  simp only [map_mul, map_neg] at hh
  linear_combination hh

variable [IsGCDMonoid R]

/-- Every polynomial relation of an actual reduced source quotient
is divisible by its independent-parameter pencil equation. -/
theorem sourcePencilEquation_dvd_iff_eval_fraction_zero
    (p q : R) (hq : q ≠ 0) (hrel : IsRelPrime p q) (P : Polynomial R) :
    sourcePencilEquation p q ∣ P ↔
      Polynomial.eval₂ (algebraMap R (FractionRing R))
        (algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q) P = 0 := by
  constructor
  · rintro ⟨Q, rfl⟩
    rw [Polynomial.eval₂_mul, sourcePencilEquation_eval_fraction p q hq, zero_mul]
  · intro hP
    apply ((sourcePencilEquation_isPrimitive p q hrel).dvd_iff_fraction_map_dvd_fraction_map
      (FractionRing R)).mpr
    rw [sourcePencilEquation_map_fraction_factor p q hq]
    have hqF : algebraMap R (FractionRing R) q ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective R (FractionRing R)).ne hq
    have hu : IsUnit (Polynomial.C (-algebraMap R (FractionRing R) q)) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hqF))
    rw [hu.mul_left_dvd]
    apply Polynomial.dvd_iff_isRoot.mpr
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hP

/-- The entire evaluation kernel of the reduced quotient is exactly
the principal ideal of its actual independent-parameter pencil equation. -/
theorem sourcePencilEquation_evaluation_kernel
    (p q : R) (hq : q ≠ 0) (hrel : IsRelPrime p q) :
    RingHom.ker (Polynomial.eval₂RingHom (algebraMap R (FractionRing R))
      (algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q)) =
      Ideal.span {sourcePencilEquation p q} := by
  ext P
  change Polynomial.eval₂ (algebraMap R (FractionRing R))
    (algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q) P = 0 ↔ _
  rw [Ideal.mem_span_singleton, sourcePencilEquation_dvd_iff_eval_fraction_zero p q hq hrel P]

end Pencil

variable {K : Type*} [Field K]

/-- The original actual Gauss parameter supplies a reduced positive-degree
homogeneous source pencil with an irreducible independent-parameter
equation and its exact evaluation kernel. -/
theorem actual_gauss_parameter_homogeneous_pencil_equation
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    ∃ p q : MvPolynomial (Fin 4) K, ∃ D : ℕ, 0 < D ∧ p ≠ 0 ∧ q ≠ 0 ∧
      p.IsHomogeneous D ∧ q.IsHomogeneous D ∧ IsRelPrime p q ∧
      Irreducible (sourcePencilEquation p q) ∧
      gaussParameterSourceHom H I e RatFunc.X =
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) p /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) q ∧
      RingHom.ker (Polynomial.eval₂RingHom
        (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)))
        (gaussParameterSourceHom H I e RatFunc.X)) = Ideal.span {sourcePencilEquation p q} := by
  obtain ⟨p, q, D, hD, hp, hq, hpH, hqH, hrel, he⟩ :=
    actual_gauss_parameter_reduced_homogeneous_source_quotient H hH I e
  refine ⟨p, q, D, hD, hp, hq, hpH, hqH, hrel,
    sourcePencilEquation_irreducible p q hq hrel, he, ?_⟩
  rw [he]
  exact sourcePencilEquation_evaluation_kernel p q hq hrel

end DimensionFourDependence
