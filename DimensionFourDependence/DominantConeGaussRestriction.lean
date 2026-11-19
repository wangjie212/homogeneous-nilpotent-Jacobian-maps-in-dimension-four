import DimensionFourDependence.ImageConeGaussRealization

/-! # A dominant parameter-preserving cone restriction has a common normal

Dominance is expressed by the exact prime kernel of polynomial
substitution at the cone generic point. It constructs the cone field
endomorphism. Preservation of the original Gauss parameter fixes the
whole Gauss field and gives proportional original normal covectors.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}
  (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

/-- A polynomial restriction with the original cone as its exact
relation prime induces a field endomorphism of its actual residue field. -/
noncomputable def dominantConeRestriction
    (P : Fin n → MvPolynomial (Fin n) K)
    (hdom : ∀ p : MvPolynomial (Fin n) K,
      algebraMap (MvPolynomial (Fin n) K) Q.ResidueField (aeval P p) = 0 ↔ p ∈ Q) :
    Q.ResidueField →ₐ[K] Q.ResidueField := by
  let f : MvPolynomial (Fin n) K →ₐ[K] Q.ResidueField :=
    (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) Q.ResidueField).comp (aeval P)
  have hker : Q = RingHom.ker f := Ideal.ext fun p => (hdom p).symm
  apply Ideal.ResidueField.liftₐ Q f hker.le
  intro p hp
  change IsUnit (f p)
  apply isUnit_iff_ne_zero.mpr
  intro hz
  exact hp ((hdom p).mp hz)

/-- The constructed dominant restriction retains the original
polynomial substitution on every cone rational function numerator. -/
theorem dominantConeRestriction_polynomial
    (P : Fin n → MvPolynomial (Fin n) K)
    (hdom : ∀ p : MvPolynomial (Fin n) K,
      algebraMap (MvPolynomial (Fin n) K) Q.ResidueField (aeval P p) = 0 ↔ p ∈ Q)
    (p : MvPolynomial (Fin n) K) :
    dominantConeRestriction Q P hdom
        (algebraMap (MvPolynomial (Fin n) K) Q.ResidueField p) =
      algebraMap (MvPolynomial (Fin n) K) Q.ResidueField (aeval P p) := by
  unfold dominantConeRestriction
  rw [Ideal.ResidueField.liftₐ_algebraMap]
  rfl

variable {F : Type*} [Field F] [Algebra K F]

/-- Homomorphisms out of the original rational Gauss parameter field
are determined by their value at that parameter. -/
theorem rational_parameter_algHom_ext (f g : RatFunc K →ₐ[K] F)
    (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  ext r
  obtain ⟨p, q, _hq, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial K) r
  simp only [map_div₀, rational_function_algHom_polynomial_value, hX]

/-- Fixing the original Gauss parameter fixes every actual normal
ratio and yields a common source/target normal with nonzero scalar.
The scalar, pivot nonvanishing and normal comparison are conclusions. -/
theorem dominant_cone_original_gauss_parameter_constructs_common_normal
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (P : Fin 4 → MvPolynomial (Fin 4) K)
    (hdom : ∀ p : MvPolynomial (Fin 4) K,
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField (aeval P p) = 0 ↔
        p ∈ imageRelationIdeal H)
    (hpreserve : dominantConeRestriction (imageRelationIdeal H) P hdom
      (imageConeGaussHom H I e RatFunc.X) = imageConeGaussHom H I e RatFunc.X) :
    ∃ α : (imageRelationIdeal H).ResidueField, α ≠ 0 ∧
      mappedPolynomialGradient
        ((algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField).comp
          (aeval P).toRingHom) I.equation =
        fun j => α * mappedPolynomialGradient
          (algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField) I.equation j := by
  let σ := dominantConeRestriction (imageRelationIdeal H) P hdom
  let ρ := algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField
  let a := imageNormalPivot H I
  have hfix : σ.comp (imageConeGaussHom H I e) = imageConeGaussHom H I e :=
    rational_parameter_algHom_ext _ _ hpreserve
  have ha : ρ (pderiv a I.equation) ≠ 0 := image_cone_normal_pivot_ne_zero H I
  have hσa : σ (ρ (pderiv a I.equation)) ≠ 0 := (map_ne_zero σ).mpr ha
  let α := σ (ρ (pderiv a I.equation)) / ρ (pderiv a I.equation)
  refine ⟨α, div_ne_zero hσa ha, ?_⟩
  funext i
  have he := DFunLike.congr_fun hfix (gaussParameterNormal H I e i)
  change σ (imageConeGaussHom H I e (gaussParameterNormal H I e i)) =
    imageConeGaussHom H I e (gaussParameterNormal H I e i) at he
  rw [imageConeGaussHom_normal, map_div₀] at he
  have hcross := (div_eq_div_iff hσa ha).mp he
  change ρ (aeval P (pderiv i I.equation)) = α * ρ (pderiv i I.equation)
  rw [← dominantConeRestriction_polynomial (imageRelationIdeal H) P hdom]
  change σ (ρ (pderiv i I.equation)) = _
  dsimp only [α]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff ha).mpr
  linear_combination hcross

end DimensionFourDependence
