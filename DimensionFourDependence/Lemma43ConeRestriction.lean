import DimensionFourDependence.FixedNormalKernelTransport
import DimensionFourDependence.ConeGaussHomogeneousFraction
import DimensionFourDependence.PrimitiveMapDegree

/-! # Lemma 4.3 in the original cone function field

The original Gauss parameter supplies its own homogeneous quotient.
Dominance and parameter preservation construct its common tangent
kernels and normals, while the local simple-pole argument contradicts
the original nilpotent Jacobian. No auxiliary geometric covectors or
local-ring hypotheses are supplied.
-/

namespace DimensionFourDependence

open MvPolynomial

section Quotient

variable {K : Type*} [Field K] {n : ℕ}
  (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

local notation "S" => MvPolynomial (Fin n) K
local notation "κ" => Q.ResidueField

/-- Preserving an actual cone rational quotient constructs the
nonzero target denominator and the polynomial cross relation modulo
the original cone equation. -/
theorem dominant_cone_preserved_quotient_cross_relation
    (R : S) (hQ : Q = Ideal.span {R}) (P : Fin n → S)
    (hdom : ∀ z : S, algebraMap S κ (aeval P z) = 0 ↔ z ∈ Q)
    (p q : S) (hq : algebraMap S κ q ≠ 0)
    (hpreserve : dominantConeRestriction Q P hdom (algebraMap S κ p / algebraMap S κ q) =
      algebraMap S κ p / algebraMap S κ q) :
    algebraMap S κ (aeval P q) ≠ 0 ∧ R ∣ aeval P p * q - p * aeval P q := by
  have hqP : algebraMap S κ (aeval P q) ≠ 0 := by
    rw [← dominantConeRestriction_polynomial Q P hdom q]
    exact (map_ne_zero (dominantConeRestriction Q P hdom)).mpr hq
  have he := hpreserve
  rw [map_div₀, dominantConeRestriction_polynomial, dominantConeRestriction_polynomial] at he
  have hcross := (div_eq_div_iff hqP hq).mp he
  have hz : algebraMap S κ (aeval P p * q - p * aeval P q) = 0 := by
    rw [map_sub, map_mul, map_mul, hcross, sub_self]
  have hm := Ideal.algebraMap_residueField_eq_zero.mp hz
  rw [hQ, Ideal.mem_span_singleton] at hm
  exact ⟨hqP, hm⟩

end Quotient

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Lemma 4.3 at the original image-cone generic point: a dominant
restriction of the primitive part cannot preserve the original
birational Gauss parameter. Dominance is the exact cone prime kernel.
All quotient presentations, nonzero tangent differentials, common
normals, common ruling kernels and local arithmetic are derived. -/
theorem no_dominant_original_gauss_parameter_preserving_cone_restriction
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ ComponentsDependent H)
    (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (g : MvPolynomial (Fin 4) K) (hg : g ≠ 0)
    (P : Fin 4 → MvPolynomial (Fin 4) K) (hHP : H = fun i => g * P i)
    (hdom : ∀ z : MvPolynomial (Fin 4) K,
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField (aeval P z) = 0 ↔
        z ∈ imageRelationIdeal H) :
    dominantConeRestriction (imageRelationIdeal H) P hdom
      (imageConeGaussHom H I e RatFunc.X) ≠ imageConeGaussHom H I e RatFunc.X := by
  intro hpreserve
  obtain ⟨p, q, m, hq, hpH, hqH, ht⟩ := original_cone_gauss_parameter_homogeneous_fraction H I e
  have hquot : dominantConeRestriction (imageRelationIdeal H) P hdom
      (algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField p /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField q) =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField p /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField q := by
    rw [← ht]
    exact hpreserve
  obtain ⟨hqP, hcross⟩ := dominant_cone_preserved_quotient_cross_relation (imageRelationIdeal H)
    I.equation (I.ideal_eq_span H hrank) P hdom p q hq hquot
  obtain ⟨α, hα, hnormal⟩ :=
    dominant_cone_original_gauss_parameter_constructs_common_normal H I e P hdom hpreserve
  have hker := dominant_cone_original_parameter_common_tangent_kernels H hd hH hind hrank I e
    P hdom hpreserve p q ht
  have htrans : Transcendental K
      (algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField p /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField q) := by
    rw [← ht]
    exact imageConeGaussHom_parameter_transcendental H I e
  exact actual_image_cone_transcendental_parameter_obstruction (imageRelationIdeal H) H hN I
    (I.ideal_eq_span H hrank) g hg P hHP p q hpH hqH hq hqP htrans hcross α hα hnormal hker

/-- An original map with Gauss dimension one constructs its primitive
part and its original Gauss parameter, for which the complete generic
cone restriction obstruction applies. No primitive factorization or
rational Gauss parametrization is a supplied auxiliary datum. -/
theorem exists_actual_primitive_part_with_lemma43_cone_obstruction
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hN : IsNilpotent (jac H)) (hind : ¬ ComponentsDependent H)
    (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1) :
    ∃ e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I),
    ∃ (g : MvPolynomial (Fin 4) K) (P : Fin 4 → MvPolynomial (Fin 4) K) (c : ℕ),
      c ≤ d - 2 ∧ g ≠ 0 ∧ g.IsHomogeneous c ∧ IsHomogMap P (d - c) ∧ IsPrimitiveVec P ∧
      H = (fun i => g * P i) ∧
      ∀ hdom : ∀ z : MvPolynomial (Fin 4) K,
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField (aeval P z) = 0 ↔
          z ∈ imageRelationIdeal H,
        dominantConeRestriction (imageRelationIdeal H) P hdom
          (imageConeGaussHom H I e RatFunc.X) ≠ imageConeGaussHom H I e RatFunc.X := by
  obtain ⟨e⟩ := actual_gauss_curve_rational_function_field H I hGauss
  obtain ⟨g, P, c, hc, hg, hgh, hP, hprim, hHP, _hdegree⟩ :=
    exists_primitive_factorization_common_degree_le_sub_two H hH hind I
  exact ⟨e, g, P, c, hc, hg, hgh, hP, hprim, hHP, fun hdom =>
    no_dominant_original_gauss_parameter_preserving_cone_restriction H hd hH hN hind hrank I e g hg P hHP hdom⟩

end DimensionFourDependence
