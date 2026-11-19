import DimensionFourDependence.ConeTangentDerivation
import DimensionFourDependence.DominantConeGaussRestriction

/-! # The original cone parameter differential detects the ruling

The actual first normal derivative annihilates the cone point.
Differentiating with the derivation supplied by each tangent vector
gives the original second-normal-pairing identity on the tangent space.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The actual first derivative of the original Gauss normal
annihilates the actual image-cone generic point. -/
theorem original_cone_gauss_normal_derivative_incidence
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I)) :
    (fun i => imageConeGaussHom H I e (rationalParameterDerivative K (gaussParameterNormal H I e i))) ⬝ᵥ
      (fun i => algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField (X i)) = 0 := by
  apply (imageConeResidueEmbedding H).injective
  change imageConeResidueEmbedding H (_ ⬝ᵥ _) = imageConeResidueEmbedding H 0
  simp only [dotProduct, map_sum, map_mul, map_zero, imageConeGaussHom_realization,
    imageConeResidueEmbedding_polynomial, aeval_X]
  exact I.parameter_normal_derivative_dot_output_eq_zero H hd hH e

variable {n : ℕ} (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

local notation "S" => MvPolynomial (Fin n) K
local notation "κ" => Q.ResidueField

omit [CharZero K] in
/-- Differentiate a ruling incidence with every actual tangent
derivation. This constructs the exact equation relating the original
rational parameter covector and the first normal derivative on T. -/
theorem cone_parameter_differential_ruling_identity
    (R : S) (hQ : Q = Ideal.span {R}) (φ : RatFunc K →ₐ[K] κ) (ν : Fin n → RatFunc K)
    (hinc : (fun i => φ (rationalParameterDerivative K (ν i))) ⬝ᵥ
      (fun i => algebraMap S κ (X i)) = 0)
    (p q : S) (ht : φ RatFunc.X = algebraMap S κ p / algebraMap S κ q)
    (v : Fin n → κ) (hv : mappedPolynomialGradient (algebraMap S κ) R ⬝ᵥ v = 0) :
    ((fun i => φ (rationalParameterDerivative K (rationalParameterDerivative K (ν i)))) ⬝ᵥ
        (fun i => algebraMap S κ (X i))) *
      (polynomialRatioCovector (algebraMap S κ) p q ⬝ᵥ v) +
      (fun i => φ (rationalParameterDerivative K (ν i))) ⬝ᵥ v = 0 := by
  obtain ⟨D, hD⟩ := cone_tangent_vector_constructs_field_derivation Q R hQ v hv
  have he := congrArg D hinc
  rw [derivation_dotProduct, map_zero] at he
  have hchain (i : Fin n) :
      D (φ (rationalParameterDerivative K (ν i))) =
        φ (rationalParameterDerivative K (rationalParameterDerivative K (ν i))) *
          (polynomialRatioCovector (algebraMap S κ) p q ⬝ᵥ v) := by
    rw [rational_parameter_chain_rule, ht]
    have hd := derivation_polynomialRatioCovector_pairing (IsScalarTower.toAlgHom K S κ) D p q
    change D (algebraMap S κ p / algebraMap S κ q) =
      polynomialRatioCovector (algebraMap S κ) p q ⬝ᵥ
        (fun j => D (algebraMap S κ (X j))) at hd
    rw [hd]
    simp only [hD]
  simp only [hchain, hD] at he
  convert he using 1
  congr 1
  simp only [dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The original homogeneous map supplies the actual ruling
incidence and cone equation, so its own Gauss parameter satisfies the
exact tangent differential identity. No incidence or tangent lift is
an additional assumption. -/
theorem original_cone_gauss_parameter_tangent_differential_identity
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (p q : MvPolynomial (Fin 4) K)
    (ht : imageConeGaussHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField p /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField q)
    (v : Fin 4 → (imageRelationIdeal H).ResidueField)
    (hv : mappedPolynomialGradient
      (algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField) I.equation ⬝ᵥ v = 0) :
    ((fun i => imageConeGaussHom H I e
        (rationalParameterDerivative K (rationalParameterDerivative K (gaussParameterNormal H I e i)))) ⬝ᵥ
        (fun i => algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField (X i))) *
      (polynomialRatioCovector
        (algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField) p q ⬝ᵥ v) +
      (fun i => imageConeGaussHom H I e (rationalParameterDerivative K (gaussParameterNormal H I e i))) ⬝ᵥ v = 0 :=
  cone_parameter_differential_ruling_identity (imageRelationIdeal H) I.equation (I.ideal_eq_span H hrank)
    (imageConeGaussHom H I e) (gaussParameterNormal H I e)
    (original_cone_gauss_normal_derivative_incidence H hd hH I e) p q ht v hv

end DimensionFourDependence
