import DimensionFourDependence.HomogeneousProjectiveSubstitution

/-! # The original Gauss parameter at a primitive boundary image

Equal-degree quotients are unchanged by the nonzero scalar relating
the primitive boundary image to its actual projective target. At a
generic source direction, equality of these parameter values gives
the original cone field's parameter-preservation identity.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Ratios

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}

/-- A homogeneous quotient of degree zero has identical values at
nonzero proportional coordinate vectors, without denominator choices. -/
theorem homogeneous_quotient_value_of_proportional
    (b y : Fin n → F) (c : F) (hc : c ≠ 0) (hby : ∀ i, b i = c * y i)
    (p q : MvPolynomial (Fin n) K) {m : ℕ} (hp : p.IsHomogeneous m) (hq : q.IsHomogeneous m) :
    aeval b p / aeval b q = aeval y p / aeval y q := by
  rw [funext hby, homogeneous_aeval_scale p hp y c, homogeneous_aeval_scale q hq y c]
  exact mul_div_mul_left _ _ (pow_ne_zero m hc)

end Ratios

universe u

variable {K κ : Type u} [Field K] [CharZero K] [Field κ] [Algebra K κ]

omit [CharZero K] in
/-- A homogeneous polynomial is nonzero at an actual generic
projective source point whenever it is nonzero in the original cone
field. Normalized projective coordinates need no affine-cone embedding. -/
theorem projective_generic_homogeneous_denominator_ne_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) (b : Fin 4 → κ) (hb : b ≠ 0)
    (hgeneric : projectiveFieldPoint (E := K) b hb = projectiveImageGenericPoint H hd hH hH0)
    (q : MvPolynomial (Fin 4) K) {m : ℕ} (hq : q.IsHomogeneous m)
    (hqcone : algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField q ≠ 0) :
    aeval b q ≠ 0 := by
  intro hz
  have hm := (projectiveFieldPoint_homogeneous_mem b hb q hq).mpr hz
  rw [hgeneric] at hm
  exact hqcone (Ideal.algebraMap_residueField_eq_zero.mpr hm)

omit [CharZero K] in
/-- At an actual generic projective source direction, equal values
of an original homogeneous parameter quotient at source and target
force its preservation in the original cone field. -/
theorem generic_projective_parameter_comparison_implies_cone_preservation
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) (P : Fin 4 → MvPolynomial (Fin 4) K) {D : ℕ} (hP : IsHomogMap P D)
    (hdom : ∀ z : MvPolynomial (Fin 4) K,
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField (aeval P z) = 0 ↔
        z ∈ imageRelationIdeal H)
    (b y : Fin 4 → κ) (hb : b ≠ 0)
    (hbgen : projectiveFieldPoint (E := K) b hb = projectiveImageGenericPoint H hd hH hH0)
    (c : κ) (hc : c ≠ 0) (hby : ∀ i, aeval b (P i) = c * y i)
    (p q : MvPolynomial (Fin 4) K) {m : ℕ} (hp : p.IsHomogeneous m) (hq : q.IsHomogeneous m)
    (hqcone : algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField q ≠ 0)
    (hcompare : aeval b p / aeval b q = aeval y p / aeval y q) :
    dominantConeRestriction (imageRelationIdeal H) P hdom
      (algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField p /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField q) =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField p /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField q := by
  let ρ := algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField
  have hqPcone : ρ (aeval P q) ≠ 0 := by
    rw [← dominantConeRestriction_polynomial (imageRelationIdeal H) P hdom]
    exact (map_ne_zero (dominantConeRestriction (imageRelationIdeal H) P hdom)).mpr hqcone
  have hqb := projective_generic_homogeneous_denominator_ne_zero H hd hH hH0 b hb hbgen q hq hqcone
  have hqPb := projective_generic_homogeneous_denominator_ne_zero H hd hH hH0 b hb hbgen
    (aeval P q) (hq.aeval P hP) hqPcone
  have hvalue : aeval b (aeval P p) / aeval b (aeval P q) = aeval b p / aeval b q := by
    rw [comp_aeval_apply P (aeval b) p, comp_aeval_apply P (aeval b) q]
    exact (homogeneous_quotient_value_of_proportional _ y c hc hby p q hp hq).trans hcompare.symm
  have hcross := (div_eq_div_iff hqPb hqb).mp hvalue
  let r := aeval P p * q - p * aeval P q
  have hr : r.IsHomogeneous (D * m + m) :=
    ((hp.aeval P hP).mul hq).sub (by simpa only [Nat.add_comm] using hp.mul (hq.aeval P hP))
  have hrb : aeval b r = 0 := by
    simp only [r, map_sub, map_mul]
    exact sub_eq_zero.mpr hcross
  have hm := (projectiveFieldPoint_homogeneous_mem b hb r hr).mpr hrb
  rw [hbgen] at hm
  have hzero : ρ r = 0 := Ideal.algebraMap_residueField_eq_zero.mpr hm
  change ρ (aeval P p * q - p * aeval P q) = 0 at hzero
  rw [map_sub, map_mul, map_mul] at hzero
  rw [map_div₀, dominantConeRestriction_polynomial, dominantConeRestriction_polynomial]
  exact (div_eq_div_iff hqPcone hqcone).mpr (sub_eq_zero.mp hzero)

/-- The primitive image of an actual projectively generic source
direction cannot be a generic original target with the same original
Gauss-parameter value. This is the generic-point exclusion used after
Lemma 4.3. Parameter comparison for the actual boundary ruling is a
separate geometric obligation. -/
theorem no_generic_original_direction_with_same_parameter_target
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hH0 : H ≠ 0) (hN : IsNilpotent (jac H)) (hind : ¬ ComponentsDependent H)
    (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (g : MvPolynomial (Fin 4) K) (hg : g ≠ 0) (P : Fin 4 → MvPolynomial (Fin 4) K)
    {D : ℕ} (hD : 0 < D) (hP : IsHomogMap P D) (hprim : IsPrimitiveVec P) (hHP : H = fun i => g * P i)
    (b y : Fin 4 → κ) (hb : b ≠ 0) (hy : y ≠ 0)
    (hbgen : projectiveFieldPoint (E := K) b hb = projectiveImageGenericPoint H hd hH hH0)
    (hygen : projectiveFieldPoint (E := K) y hy = projectiveImageGenericPoint H hd hH hH0)
    (c : κ) (hc : c ≠ 0) (hby : ∀ i, aeval b (P i) = c * y i)
    (p q : MvPolynomial (Fin 4) K) {m : ℕ} (hp : p.IsHomogeneous m) (hq : q.IsHomogeneous m)
    (hqcone : algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField q ≠ 0)
    (ht : imageConeGaussHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField p /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField q)
    (hcompare : aeval b p / aeval b q = aeval y p / aeval y q) : False := by
  have hprojective := generic_source_and_target_construct_projective_restriction_dominance H hd hH hH0 hrank I
    P hD hP hprim b y hb hy hbgen hygen c hc hby
  have hcone := original_projective_restriction_dominance_constructs_cone_kernel H hd hH hH0 hrank I
    P hD hP hprim hprojective
  have hfixed := generic_projective_parameter_comparison_implies_cone_preservation H hd hH hH0 P hP hcone
    b y hb hbgen c hc hby p q hp hq hqcone hcompare
  apply no_dominant_original_gauss_parameter_preserving_cone_restriction H hd hH hN hind hrank I e g hg P hHP hcone
  rw [ht]
  exact hfixed

end DimensionFourDependence
