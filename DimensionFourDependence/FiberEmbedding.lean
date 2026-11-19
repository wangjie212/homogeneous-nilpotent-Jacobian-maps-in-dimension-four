import DimensionFourDependence.FullSourceComponents

/-! # Embedding a generic fiber field using its polynomial relations -/

namespace DimensionFourDependence

open MvPolynomial

variable {L F G : Type*} [Field L] [Field F] [Field G] [Algebra L F] [Algebra L G] {n : ℕ}

/-- The canonical quotient fraction-field equivalence evaluates polynomial classes. -/
theorem fiberQuotientFractionEquiv_aeval (x : Fin n → F)
    (hx : IntermediateField.adjoin L (Set.range x) = ⊤) (p : MvPolynomial (Fin n) L) :
    fiberQuotientFractionEquiv x hx
      (algebraMap (MvPolynomial (Fin n) L ⧸ fiberVanishingIdeal (L := L) x)
        (FractionRing (MvPolynomial (Fin n) L ⧸ fiberVanishingIdeal (L := L) x))
        (Ideal.Quotient.mk _ p)) = aeval x p := by
  change fiberCoordinateFractionHom (L := L) x
    ((IsFractionRing.algEquivOfAlgEquiv
      (K := FractionRing (MvPolynomial (Fin n) L ⧸ fiberVanishingIdeal (L := L) x))
      (L := FractionRing (fiberCoordinateAlgebra (L := L) x))
      (fiberCoordinateQuotientEquiv (L := L) x))
      (algebraMap (MvPolynomial (Fin n) L ⧸ fiberVanishingIdeal (L := L) x)
        (FractionRing (MvPolynomial (Fin n) L ⧸ fiberVanishingIdeal (L := L) x))
        (Ideal.Quotient.mk _ p))) = _
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change IsFractionRing.lift (show Function.Injective (fiberCoordinateAlgebra (L := L) x).val
    from Subtype.val_injective)
    (algebraMap (fiberCoordinateAlgebra (L := L) x) _
      (fiberCoordinateQuotientEquiv x (Ideal.Quotient.mk _ p))) = _
  rw [IsFractionRing.lift_algebraMap]
  rfl

/-- A point with the same polynomial relations embeds the original
coordinate function field and carries its coordinates to that point. -/
theorem exists_fiber_embedding_of_relations_eq (x : Fin n → F) (z : Fin n → G)
    (hx : IntermediateField.adjoin L (Set.range x) = ⊤)
    (hrel : fiberVanishingIdeal (L := L) z = fiberVanishingIdeal (L := L) x) :
    ∃ f : F →ₐ[L] G, ∀ i, f (x i) = z i := by
  let P := fiberVanishingIdeal (L := L) x
  have hvan : ∀ a : MvPolynomial (Fin n) L, a ∈ P → aeval z a = 0 := by
    intro a ha
    exact hrel.ge ha
  let q : (MvPolynomial (Fin n) L ⧸ P) →ₐ[L] G := Ideal.Quotient.liftₐ P (aeval z) hvan
  have hqi : Function.Injective q :=
    RingHom.lift_injective_of_ker_le_ideal P hvan hrel.le
  let f₀ : FractionRing (MvPolynomial (Fin n) L ⧸ P) →ₐ[L] G := IsFractionRing.liftAlgHom hqi
  let e := fiberQuotientFractionEquiv x hx
  refine ⟨f₀.comp e.symm.toAlgHom, ?_⟩
  intro i
  have he : e (algebraMap (MvPolynomial (Fin n) L ⧸ P)
      (FractionRing (MvPolynomial (Fin n) L ⧸ P)) (Ideal.Quotient.mk P (X i))) = x i := by
    simpa only [aeval_X] using fiberQuotientFractionEquiv_aeval x hx (X i)
  change f₀ (e.symm (x i)) = z i
  rw [← he, e.symm_apply_apply]
  change IsFractionRing.lift hqi (algebraMap (MvPolynomial (Fin n) L ⧸ P)
    (FractionRing (MvPolynomial (Fin n) L ⧸ P)) (Ideal.Quotient.mk P (X i))) = z i
  rw [IsFractionRing.lift_algebraMap]
  exact aeval_X z i

end DimensionFourDependence
