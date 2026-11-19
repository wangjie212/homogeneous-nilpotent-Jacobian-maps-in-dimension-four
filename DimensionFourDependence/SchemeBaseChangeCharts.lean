import DimensionFourDependence.Defs
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Tensor affine squares and gluing a global coefficient base change -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

/-- The actual spectrum of a coefficient tensor product is the
categorical affine base change, with both specified tensor inclusions. -/
theorem spectrum_tensor_coefficient_isPullback
    (C A E : Type u) [CommRing C] [CommRing A] [CommRing E]
    [Algebra C A] [Algebra C E] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A →ₐ[C] A ⊗[C] E).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : E →ₐ[C] A ⊗[C] E).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap C A)))
      (Spec.map (CommRingCat.ofHom (algebraMap C E))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct C A E)

/-- Compatible actual charts of the inverse-image opens suffice to
prove the entire global square is a categorical base change. -/
theorem scheme_isPullback_of_chart_squares
    {W X Y Z : Scheme.{u}} (fWX : W ⟶ X) (fWY : W ⟶ Y) (fXZ : X ⟶ Z) (fYZ : Y ⟶ Z)
    (𝒰 : X.OpenCover) (V : 𝒰.I₀ → Scheme.{u})
    (j : ∀ i, V i ⟶ W) (r : ∀ i, V i ⟶ 𝒰.X i)
    (hopen : ∀ i, IsPullback (j i) (r i) fWX (𝒰.f i))
    (hbase : ∀ i, IsPullback (r i) (j i ≫ fWY) (𝒰.f i ≫ fXZ) fYZ) :
    IsPullback fWX fWY fXZ fYZ := by
  apply Scheme.isPullback_of_openCover fWX fWY fXZ fYZ 𝒰
  intro i
  change IsPullback (pullback.snd fWX (𝒰.f i))
    (pullback.fst fWX (𝒰.f i) ≫ fWY) (𝒰.f i ≫ fXZ) fYZ
  apply (hbase i).of_iso (hopen i).isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using (hopen i).isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc, IsPullback.isoPullback_hom_fst]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

end DimensionFourDependence
