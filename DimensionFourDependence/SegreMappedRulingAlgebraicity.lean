import DimensionFourDependence.SegreBoundaryParameterField

/-! # Original Segre algebraicity under a specified coefficient embedding -/

namespace DimensionFourDependence

open MvPolynomial Matrix
attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

universe u
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]

/-- A specified embedding of the actual algebraic coefficient field
transports the original ruling algebraicity theorem to the exact mapped
parameter. No identification of boundary constants with the source constants is assumed. -/
theorem nongeneric_normalized_segre_point_algebraic_over_mapped_parameter
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    (hY : AlgebraicIndependent K (segreOriginalOutputTriple H))
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hH0 : H ≠ 0)
    (hind : ¬ComponentsDependent H) (hSegre : H 0 * H 3 - H 1 * H 2 = 0)
    (j : Fin 3) (hj : j ≠ 0) (κ : Type u) [Field κ] [Algebra K κ]
    (f : coefficientField (K := K) (segreOriginalOutputTriple H) →ₐ[K] κ)
    (t : κ) (ht : f (segreCoefficientRulingParameter (segreOriginalOutputTriple H) j) = t)
    (b : Fin 4 → κ) (hb : b ≠ 0) (a : Fin 4) (ha : b a = 1)
    (hkernel : segreRulingMatrix j t *ᵥ b = 0)
    (hng : projectiveFieldPoint (E := K) b hb ≠ projectiveImageGenericPoint H hd hH hH0) :
    ∀ i, IsAlgebraic (IntermediateField.adjoin K ({t} : Set κ)) (b i) := by
  let : Algebra (coefficientField (K := K) (segreOriginalOutputTriple H)) κ := f.toRingHom.toAlgebra
  let : IsScalarTower K (coefficientField (K := K) (segreOriginalOutputTriple H)) κ :=
    IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  have hk : (segreRulingMatrix j (segreRulingFieldParameter (segreOriginalOutputTriple H) hY j hj)).map
      ((algebraMap (coefficientField (K := K) (segreOriginalOutputTriple H)) κ).comp
        (segreRulingFieldCoefficientHom (segreOriginalOutputTriple H) hY j hj).toRingHom) *ᵥ b = 0 := by
    rw [segreRulingMatrix_map]
    change segreRulingMatrix j (f (segreRulingFieldCoefficientHom (segreOriginalOutputTriple H) hY j hj
      (segreRulingFieldParameter (segreOriginalOutputTriple H) hY j hj))) *ᵥ b = 0
    rw [segreRulingFieldCoefficientHom_parameter, ht]
    exact hkernel
  have halg := nongeneric_normalized_original_segre_ruling_point_isAlgebraic
    H hY hd hH hH0 hind hSegre j hj κ b hb a ha hk hng
  rw [segreBoundaryRulingField_eq_adjoin_parameter] at halg
  change ∀ i, IsAlgebraic (IntermediateField.adjoin K
    ({f (segreCoefficientRulingParameter (segreOriginalOutputTriple H) j)} : Set κ)) (b i) at halg
  rw [ht] at halg
  exact halg

end DimensionFourDependence
