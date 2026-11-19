import DimensionFourDependence.DominantConeGaussRestriction

/-! # Coordinate generators determine derivatives on the cone function field -/

namespace DimensionFourDependence

open MvPolynomial

universe u
variable {K : Type u} [Field K] {n : ℕ}
  (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

/-- A derivation killing the images of the cone coordinates under a
field homomorphism kills its image on the entire cone function field. -/
theorem cone_field_derivation_kills_image_of_coordinates
    (σ : Q.ResidueField →ₐ[K] Q.ResidueField)
    (D : Derivation K Q.ResidueField Q.ResidueField)
    (hD : ∀ i, D (σ (algebraMap (MvPolynomial (Fin n) K) Q.ResidueField (X i))) = 0)
    (z : Q.ResidueField) : D (σ z) = 0 := by
  have hp : ∀ p : MvPolynomial (Fin n) K,
      D (σ (algebraMap (MvPolynomial (Fin n) K) Q.ResidueField p)) = 0 := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
        change D (σ (algebraMap K Q.ResidueField a)) = 0
        rw [σ.commutes, D.map_algebraMap]
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
    | mul_X a i ha => simp only [map_mul, D.leibniz, ha, hD, smul_zero, zero_add]
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin n) K ⧸ Q) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [Ideal.algebraMap_quotient_residueField_mk, map_div₀, D.leibniz_div, hp,
    smul_zero, sub_zero]

end DimensionFourDependence
