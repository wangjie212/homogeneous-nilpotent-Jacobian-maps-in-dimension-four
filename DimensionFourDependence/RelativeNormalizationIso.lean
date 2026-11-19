import DimensionFourDependence.IntegralSchemeNormalization

/-! # Relative normalization respects an isomorphism of the whole defining arrow -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y X' Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : X' ⟶ Y') [QuasiCompact f] [QuasiSeparated f]
  [QuasiCompact g] [QuasiSeparated g]

/-- The reverse isomorphisms give the reverse compatible arrow square. -/
theorem normalization_arrow_iso_reverse_square
    (i : X ≅ X') (j : Y ≅ Y') (h : i.hom ≫ g = f ≫ j.hom) : i.inv ≫ f = g ≫ j.inv := by
  have h' : i.inv ≫ f ≫ j.hom = g := by
    rw [← h, Iso.inv_hom_id_assoc]
  have h'' := congrArg (fun k => k ≫ j.inv) h'
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h''

/-- The relative normalization map induced by an isomorphism of
both source and target, with its specified commutative arrow square. -/
noncomputable def relativeNormalizationArrowIsoHom
    (i : X ≅ X') (j : Y ≅ Y') (h : i.hom ≫ g = f ≫ j.hom) : f.normalization ⟶ g.normalization := by
  let : IsIntegralHom (g.fromNormalization ≫ j.inv) := inferInstance
  apply f.normalizationDesc (i.hom ≫ g.toNormalization) (g.fromNormalization ≫ j.inv)
  simp only [Category.assoc, Scheme.Hom.toNormalization_fromNormalization_assoc]
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The normalization map retains the actual defining source morphism. -/
theorem relativeNormalizationArrowIsoHom_toNormalization
    (i : X ≅ X') (j : Y ≅ Y') (h : i.hom ≫ g = f ≫ j.hom) :
    f.toNormalization ≫ relativeNormalizationArrowIsoHom f g i j h = i.hom ≫ g.toNormalization := by
  unfold relativeNormalizationArrowIsoHom
  exact f.toNormalization_normalizationDesc _ _ _

/-- The normalization map retains the actual target projection. -/
theorem relativeNormalizationArrowIsoHom_fromNormalization
    (i : X ≅ X') (j : Y ≅ Y') (h : i.hom ≫ g = f ≫ j.hom) :
    relativeNormalizationArrowIsoHom f g i j h ≫ g.fromNormalization = f.fromNormalization ≫ j.hom := by
  unfold relativeNormalizationArrowIsoHom
  apply (cancel_mono j.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact f.normalizationDesc_comp _ _ _

/-- Uniqueness in the normalization universal property detects the identity. -/
theorem relative_normalization_endomorphism_eq_id
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : f.normalization ⟶ f.normalization)
    (ha : f.toNormalization ≫ a = f.toNormalization)
    (hb : a ≫ f.fromNormalization = f.fromNormalization) : a = 𝟙 _ := by
  exact Scheme.Hom.normalization.hom_ext f a (𝟙 _) f.fromNormalization
    (by simpa only [Category.comp_id] using ha) hb (by simp)

/-- An actual isomorphism of the defining arrows gives an actual
isomorphism of their relative normalizations, by the universal property. -/
noncomputable def relativeNormalizationArrowIso
    (i : X ≅ X') (j : Y ≅ Y') (h : i.hom ≫ g = f ≫ j.hom) : f.normalization ≅ g.normalization := by
  let a := relativeNormalizationArrowIsoHom f g i j h
  let b := relativeNormalizationArrowIsoHom g f i.symm j.symm
    (normalization_arrow_iso_reverse_square f g i j h)
  refine { hom := a, inv := b, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply relative_normalization_endomorphism_eq_id f
    · dsimp only [a, b]
      rw [← Category.assoc, relativeNormalizationArrowIsoHom_toNormalization,
        Category.assoc, relativeNormalizationArrowIsoHom_toNormalization]
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
    · dsimp only [a, b]
      rw [Category.assoc, relativeNormalizationArrowIsoHom_fromNormalization,
        ← Category.assoc, relativeNormalizationArrowIsoHom_fromNormalization]
      simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · apply relative_normalization_endomorphism_eq_id g
    · dsimp only [a, b]
      rw [← Category.assoc, relativeNormalizationArrowIsoHom_toNormalization,
        Category.assoc, relativeNormalizationArrowIsoHom_toNormalization]
      simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]
    · dsimp only [a, b]
      rw [Category.assoc, relativeNormalizationArrowIsoHom_fromNormalization,
        ← Category.assoc, relativeNormalizationArrowIsoHom_fromNormalization]
      simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The normalization isomorphism preserves its actual source factorization. -/
theorem relativeNormalizationArrowIso_toNormalization
    (i : X ≅ X') (j : Y ≅ Y') (h : i.hom ≫ g = f ≫ j.hom) :
    f.toNormalization ≫ (relativeNormalizationArrowIso f g i j h).hom = i.hom ≫ g.toNormalization :=
  relativeNormalizationArrowIsoHom_toNormalization f g i j h

/-- The normalization isomorphism preserves its actual target factorization. -/
theorem relativeNormalizationArrowIso_fromNormalization
    (i : X ≅ X') (j : Y ≅ Y') (h : i.hom ≫ g = f ≫ j.hom) :
    (relativeNormalizationArrowIso f g i j h).hom ≫ g.fromNormalization = f.fromNormalization ≫ j.hom :=
  relativeNormalizationArrowIsoHom_fromNormalization f g i j h

end DimensionFourDependence
