import DimensionFourDependence.DeterminantShearAlphaOnly
import DimensionFourDependence.DeterminantShearCoefficientPolarization

/-! # Lemma 6.2: constructive tameness of every determinant shear -/

namespace DimensionFourDependence.DeterminantShear

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The complete constructive shear lemma in its original coordinates.
Both finite polarizations and both actual quadratic flows have been
proved over the original characteristic-zero field. -/
theorem automorphism4_tame (f : MvPolynomial (Fin 3) K) :
    automorphism4 f ∈ Tame.subgroup K 4 :=
  automorphism4_tame_of_alpha_only automorphism4_alpha_only_tame f

/-- **Lemma 6.2**, with exact polynomial coordinate identities and
actual membership in the four-variable tame subgroup. -/
theorem lemma_6_2 (f : MvPolynomial (Fin 3) K) :
    ∃ e : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K,
      e ∈ Tame.subgroup K 4 ∧
      ∀ j, e (X j) =
        ![X 0 + X 3 * aeval ![X 2 * X 0 - X 3 * X 1, X 2, X 3] f,
          X 1 + X 2 * aeval ![X 2 * X 0 - X 3 * X 1, X 2, X 3] f, X 2, X 3] j := by
  refine ⟨automorphism4 f, automorphism4_tame f, ?_⟩
  intro j
  exact automorphism4_X f j

/-- The last sentence of Lemma 6.2: after any actual affine coordinate
change, including an affine change of the two coefficient coordinates,
the conjugated determinant shear remains tame over the original field. -/
theorem lemma_6_2_affine_coordinates (f : MvPolynomial (Fin 3) K)
    (A : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (hA : Tame.IsAffine A) :
    A⁻¹ * automorphism4 f * A ∈ Tame.subgroup K 4 := by
  have hAt : A ∈ Tame.subgroup K 4 := Subgroup.subset_closure (Or.inl hA)
  exact (Tame.subgroup K 4).mul_mem
    ((Tame.subgroup K 4).mul_mem ((Tame.subgroup K 4).inv_mem hAt) (automorphism4_tame f)) hAt

end DimensionFourDependence.DeterminantShear
