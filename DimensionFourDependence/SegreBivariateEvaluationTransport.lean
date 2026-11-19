import DimensionFourDependence.SegreCommonFieldBivariateDescent

/-! # Exact original bivariate identities under compatible field embeddings -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {K F E : Type u} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]

/-- The specified compatible embedding preserves the entire bivariate
evaluation at the two specified original coordinate values. -/
theorem bivariate_polynomial_evaluation_algHom
    (φ : F →ₐ[K] E) (s t : F) (B : Polynomial (Polynomial K)) :
    φ (Polynomial.eval₂ (Polynomial.aeval t).toRingHom s B) =
      Polynomial.eval₂ (Polynomial.aeval (φ t)).toRingHom (φ s) B := by
  induction B using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.eval₂_add, map_add, hP, hQ]
  | monomial n P =>
    simp only [Polynomial.eval₂_monomial, map_mul, map_pow]
    change φ (Polynomial.aeval t P) * φ s ^ n = Polynomial.aeval (φ t) P * φ s ^ n
    rw [← Polynomial.aeval_algHom_apply φ t P]

/-- The exact original normalized bivariate identity maps through any
specified compatible field embedding retaining the first three outputs. -/
theorem segre_bivariate_normalized_pairing_map_of_coordinate_images
    (φ : F →ₐ[K] E) (Y : Fin 4 → F) (Z : Fin 4 → E)
    (hcoord : ∀ i : Fin 3, φ (Y i.castSucc) = Z i.castSucc)
    (f : F) (g : E) (hf : φ f = g) (d : ℕ)
    (hpoly : SegreBivariateNormalizedPairingPolynomial K Y f d) :
    SegreBivariateNormalizedPairingPolynomial K Z g d := by
  have hcast0 : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
  have hcast1 : (1 : Fin 3).castSucc = (1 : Fin 4) := by decide
  have hcast2 : (2 : Fin 3).castSucc = (2 : Fin 4) := by decide
  have h0 : φ (Y 0) = Z 0 := by simpa only [hcast0] using hcoord 0
  have h1 : φ (Y 1) = Z 1 := by simpa only [hcast1] using hcoord 1
  have h2 : φ (Y 2) = Z 2 := by simpa only [hcast2] using hcoord 2
  obtain ⟨B, hB, hdegree, hcoeffDegree, hvalue⟩ := hpoly
  refine ⟨B, hB, hdegree, hcoeffDegree, ?_⟩
  have he := congrArg φ hvalue
  simpa only [map_div₀, map_pow, bivariate_polynomial_evaluation_algHom, h0, h1, h2, hf] using he

/-- Faithfulness of the specified compatible embedding reflects the
original normalized bivariate identity, retaining the same original-field
polynomial and both of its independent degree bounds. -/
theorem segre_bivariate_normalized_pairing_reflects_of_coordinate_images
    (φ : F →ₐ[K] E) (Y : Fin 4 → F) (Z : Fin 4 → E)
    (hcoord : ∀ i : Fin 3, φ (Y i.castSucc) = Z i.castSucc)
    (f : F) (g : E) (hf : φ f = g) (d : ℕ)
    (hpoly : SegreBivariateNormalizedPairingPolynomial K Z g d) :
    SegreBivariateNormalizedPairingPolynomial K Y f d := by
  have hcast0 : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
  have hcast1 : (1 : Fin 3).castSucc = (1 : Fin 4) := by decide
  have hcast2 : (2 : Fin 3).castSucc = (2 : Fin 4) := by decide
  have h0 : φ (Y 0) = Z 0 := by simpa only [hcast0] using hcoord 0
  have h1 : φ (Y 1) = Z 1 := by simpa only [hcast1] using hcoord 1
  have h2 : φ (Y 2) = Z 2 := by simpa only [hcast2] using hcoord 2
  obtain ⟨B, hB, hdegree, hcoeffDegree, hvalue⟩ := hpoly
  refine ⟨B, hB, hdegree, hcoeffDegree, ?_⟩
  apply φ.injective
  change φ (f ^ d / (Y 0) ^ (d + 1)) =
    φ (Polynomial.eval₂ (Polynomial.aeval (Y 2 / Y 0)).toRingHom (Y 1 / Y 0) B)
  rw [bivariate_polynomial_evaluation_algHom]
  simpa only [map_div₀, map_pow, h0, h1, h2, hf] using hvalue

end DimensionFourDependence
