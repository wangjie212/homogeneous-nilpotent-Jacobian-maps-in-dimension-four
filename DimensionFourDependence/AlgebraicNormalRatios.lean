import DimensionFourDependence.GaussImageDimension
import DimensionFourDependence.ConstantField

/-! # Algebraic ratios of equally homogeneous polynomials are constant

Every coordinate derivation kills an algebraic rational quotient in
characteristic zero. Clearing the quotient derivative gives the actual
polynomial Wronskian identities. The checked homogeneous proportionality
theorem therefore supplies the constant over the original coefficient field.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- An algebraic quotient of equally homogeneous polynomials is a
constant quotient over the original field, without algebraic closedness. -/
theorem homogeneous_polynomial_algebraic_quotient_proportional
    (f g : MvPolynomial (Fin 4) K) {d : ℕ}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d) (hf0 : f ≠ 0)
    (halg : IsAlgebraic K
      (algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) g /
        algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) f)) :
    ∃ c : K, g = c • f := by
  have hfF : algebraMap (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K)) f ≠ 0 := by
    intro hz
    apply hf0
    apply IsFractionRing.injective (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
    simpa only [map_zero] using hz
  apply proportional_of_wronskian hf hg hf0
  intro j
  have hz := derivation_zero_of_isAlgebraic (rationalPartial (K := K) j) _ halg
  rw [Derivation.leibniz_div] at hz
  simp only [smul_eq_mul] at hz
  have hw := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (inv_ne_zero hfF)))
  rw [rationalPartial_polynomial, rationalPartial_polynomial] at hw
  apply IsFractionRing.injective (MvPolynomial (Fin 4) K) (FractionRing (MvPolynomial (Fin 4) K))
  simpa only [map_mul] using hw

/-- Zero transcendence degree of the actual projective-normal field
makes every actual normal coordinate proportional over the original field. -/
theorem ImageRelationWitness.normal_constant_vector_of_gauss_image_dimension_zero
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (I : ImageRelationWitness H) (hzero : gaussImageDimension H I = 0) :
    ∃ c : Fin 4 → K, c ≠ 0 ∧ ∀ i, imageRelationNormal H I.equation i =
      c i • imageRelationNormal H I.equation (imageNormalPivot H I) := by
  let ν := rationalImageNormal H I.equation
  let a := imageNormalPivot H I
  let L := projectiveRatioField (K := K) ν a
  let : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.mp hzero
  have hp : imageRelationNormal H I.equation a ≠ 0 := by
    intro hz
    exact imageNormalPivot_ne_zero H I (by simp only [rationalImageNormal, a, hz, map_zero])
  have hprop (i : Fin 4) : ∃ c : K, imageRelationNormal H I.equation i =
      c • imageRelationNormal H I.equation a := by
    apply homogeneous_polynomial_algebraic_quotient_proportional _ _
      (I.normal_homogeneous H hH a) (I.normal_homogeneous H hH i) hp
    have hm : ν i / ν a ∈ L := IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
    have ha := Algebra.IsAlgebraic.isAlgebraic (R := K) (⟨ν i / ν a, hm⟩ : L)
    exact ha.algHom (IsScalarTower.toAlgHom K L (FractionRing (MvPolynomial (Fin 4) K)))
  choose c hc using hprop
  refine ⟨c, ?_, hc⟩
  intro hz
  apply hp
  rw [hc a, congrFun hz a, Pi.zero_apply, zero_smul]

end DimensionFourDependence
