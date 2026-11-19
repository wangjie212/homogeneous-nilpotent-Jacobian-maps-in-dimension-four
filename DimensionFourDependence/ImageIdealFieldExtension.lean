import DimensionFourDependence.ImageHypersurface
import DimensionFourDependence.ScalarExtensionRank

/-! # Polynomial image ideals commute with extension of the coefficient field

The image coordinate quotient embeds into the original source polynomial
ring. Tensoring this embedding with a field extension remains injective.
The polynomial quotient base-change equivalence identifies its domain
with the quotient by the extended image ideal. The resulting embedding
then identifies that ideal with the actual extended polynomial-map kernel.
-/

namespace DimensionFourDependence

open MvPolynomial TensorProduct

variable {K : Type*} [Field K]

/-- The original image coordinate quotient embeds in the source polynomial ring. -/
noncomputable def imageCoordinateQuotientEmbedding (H : Fin 4 → MvPolynomial (Fin 4) K) :
    (MvPolynomial (Fin 4) K ⧸ imageRelationIdeal H) →ₐ[K] MvPolynomial (Fin 4) K := by
  let f : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) K := aeval H
  exact f.range.val.comp (Ideal.quotientKerEquivRange f).toAlgHom

/-- This is the actual first-isomorphism coordinate embedding, hence injective. -/
theorem imageCoordinateQuotientEmbedding_injective (H : Fin 4 → MvPolynomial (Fin 4) K) :
    Function.Injective (imageCoordinateQuotientEmbedding H) := by
  let f : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) K := aeval H
  exact Subtype.val_injective.comp (Ideal.quotientKerEquivRange f).injective

/-- The coordinate embedding evaluates each original polynomial at the polynomial map. -/
theorem imageCoordinateQuotientEmbedding_mk (H : Fin 4 → MvPolynomial (Fin 4) K)
    (P : MvPolynomial (Fin 4) K) :
    imageCoordinateQuotientEmbedding H (Ideal.Quotient.mk (imageRelationIdeal H) P) = aeval H P := by
  let f : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) K := aeval H
  change ((Ideal.quotientKerEquivRange f) (Ideal.Quotient.mk (imageRelationIdeal H) P) :
    MvPolynomial (Fin 4) K) = f P
  simp only [Ideal.quotientKerEquivRange]
  rfl

variable (E : Type*) [Field E] [Algebra K E]

/-- Tensoring the original coordinate embedding gives an embedding of the
quotient by the extended relations into the extended source polynomial ring. -/
noncomputable def extendedImageCoordinateEmbedding (H : Fin 4 → MvPolynomial (Fin 4) K) :
    (MvPolynomial (Fin 4) E ⧸ extendCoefficientIdeal E (imageRelationIdeal H)) →ₐ[E]
      MvPolynomial (Fin 4) E :=
  ((MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) K E).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id E E) (imageCoordinateQuotientEmbedding H))).comp
      (polynomialQuotientBaseChangeEquiv E (imageRelationIdeal H)).symm.toAlgHom

/-- Field extensions are flat, so the extended coordinate embedding is injective. -/
theorem extendedImageCoordinateEmbedding_injective (H : Fin 4 → MvPolynomial (Fin 4) K) :
    Function.Injective (extendedImageCoordinateEmbedding E H) := by
  have hmap : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id E E) (imageCoordinateQuotientEmbedding H)) := by
    change Function.Injective ((imageCoordinateQuotientEmbedding H).toLinearMap.baseChange E)
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (imageCoordinateQuotientEmbedding_injective H)
  exact (MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) K E).injective.comp
    (hmap.comp (polynomialQuotientBaseChangeEquiv E (imageRelationIdeal H)).symm.injective)

/-- On original-field polynomials the extended embedding is the scalar extension
of the actual polynomial-map evaluation. -/
theorem extendedImageCoordinateEmbedding_mk_map (H : Fin 4 → MvPolynomial (Fin 4) K)
    (P : MvPolynomial (Fin 4) K) :
    extendedImageCoordinateEmbedding E H
      (Ideal.Quotient.mk (extendCoefficientIdeal E (imageRelationIdeal H))
        (MvPolynomial.map (algebraMap K E) P)) = MvPolynomial.map (algebraMap K E) (aeval H P) := by
  let e := polynomialQuotientBaseChangeEquiv E (imageRelationIdeal H)
  have ht : e.symm (Ideal.Quotient.mk (extendCoefficientIdeal E (imageRelationIdeal H))
      (MvPolynomial.map (algebraMap K E) P)) = (1 : E) ⊗ₜ[K] Ideal.Quotient.mk (imageRelationIdeal H) P := by
    apply e.injective
    rw [e.apply_symm_apply, polynomialQuotientBaseChangeEquiv_tmul, one_smul]
  change (MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) K E)
    ((Algebra.TensorProduct.map (AlgHom.id E E) (imageCoordinateQuotientEmbedding H))
      (e.symm (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap K E) P)))) = _
  rw [ht, Algebra.TensorProduct.map_tmul, imageCoordinateQuotientEmbedding_mk]
  simp

/-- The coordinate embedding factors the evaluation of the actual scalar-extended map. -/
theorem extendedImageCoordinateEmbedding_comp_mk (H : Fin 4 → MvPolynomial (Fin 4) K) :
    (extendedImageCoordinateEmbedding E H).comp
      (Ideal.Quotient.mkₐ E (extendCoefficientIdeal E (imageRelationIdeal H))) =
      aeval (fun i => MvPolynomial.map (algebraMap K E) (H i)) := by
  apply MvPolynomial.algHom_ext
  intro i
  change extendedImageCoordinateEmbedding E H (Ideal.Quotient.mk _ (X i)) = _
  simpa only [MvPolynomial.map_X, aeval_X] using
    extendedImageCoordinateEmbedding_mk_map E H (X i)

/-- Extending the image relation ideal gives exactly the actual image ideal
of the scalar-extended polynomial map. -/
theorem imageRelationIdeal_scalar_extension (H : Fin 4 → MvPolynomial (Fin 4) K) :
    extendCoefficientIdeal E (imageRelationIdeal H) =
      imageRelationIdeal (fun i => MvPolynomial.map (algebraMap K E) (H i)) := by
  ext P
  have he := DFunLike.congr_fun (extendedImageCoordinateEmbedding_comp_mk E H) P
  change extendedImageCoordinateEmbedding E H (Ideal.Quotient.mk _ P) =
    aeval (fun i => MvPolynomial.map (algebraMap K E) (H i)) P at he
  change P ∈ extendCoefficientIdeal E (imageRelationIdeal H) ↔
    aeval (fun i => MvPolynomial.map (algebraMap K E) (H i)) P = 0
  constructor
  · intro hP
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hP, map_zero] at he
    exact he.symm
  · intro hP
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply extendedImageCoordinateEmbedding_injective E H
    simpa only [map_zero] using he.trans hP

/-- The original image ideal remains prime after every coefficient-field extension. -/
theorem imageRelationIdeal_scalar_extension_isPrime (H : Fin 4 → MvPolynomial (Fin 4) K) :
    (extendCoefficientIdeal E (imageRelationIdeal H)).IsPrime := by
  rw [imageRelationIdeal_scalar_extension]
  infer_instance

end DimensionFourDependence
