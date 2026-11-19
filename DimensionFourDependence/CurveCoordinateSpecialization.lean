import DimensionFourDependence.TranscendenceDegreeSpecialization
import DimensionFourDependence.GeneratedFieldDimension
import DimensionFourDependence.OutputCoordinateFieldEquiv
import DimensionFourDependence.FiberEmbedding

/-! # Nonconstant specialization of an actual curve preserves its function field

An actual coordinate quotient with transcendence degree one cannot have
a new prime kernel under a specialization with a transcendental coordinate.
The actual relation ideals coincide. The checked generic-point embedding
then gives an actual function-field embedding with the required coordinate
values; no injectivity or field comparison is assumed separately.
-/

namespace DimensionFourDependence

open MvPolynomial

universe u

variable {K F E : Type u} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E] {n : ℕ}

/-- The actual prime coordinate quotient and actual generated field
have identical transcendence degree over the original coefficient field. -/
theorem coordinateQuotient_trdeg_eq_generatedField (x : Fin n → F) :
    Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ fiberVanishingIdeal (L := K) x) =
      Algebra.trdeg K (fullOutputField (K := K) x) :=
  (fiberCoordinateQuotientEquiv (L := K) x).trdeg_eq.trans
    (generatedField_trdeg_eq_generatedAlgebra (K := K) (Set.range x)).symm

/-- A specialization of an actual curve with one transcendental
coordinate preserves exactly all original polynomial relations. -/
theorem curve_coordinate_relations_equal_of_transcendental_specialization
    (x : Fin n → F) (y : Fin n → E)
    (hdim : Algebra.trdeg K (fullOutputField (K := K) x) = 1)
    (hrel : ∀ P : MvPolynomial (Fin n) K, aeval x P = 0 → aeval y P = 0)
    (i : Fin n) (hy : Transcendental K (y i)) :
    fiberVanishingIdeal (L := K) y = fiberVanishingIdeal (L := K) x := by
  let I := fiberVanishingIdeal (L := K) x
  let g : (MvPolynomial (Fin n) K ⧸ I) →ₐ[K] E := Ideal.Quotient.liftₐ I (aeval y) hrel
  have hA : Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) = 1 :=
    (coordinateQuotient_trdeg_eq_generatedField x).trans hdim
  have hgX : g (Ideal.Quotient.mk I (X i)) = y i := by
    change aeval y (X i) = y i
    exact aeval_X y i
  have hnzero : Algebra.trdeg K g.range ≠ 0 := by
    intro hz
    let : Algebra.IsAlgebraic K g.range := trdeg_eq_zero_iff.mp hz
    let z : g.range := ⟨g (Ideal.Quotient.mk I (X i)), ⟨_, rfl⟩⟩
    have ha := (Algebra.IsAlgebraic.isAlgebraic (R := K) z).algHom g.range.val
    apply hy
    simpa only [z, Subalgebra.val_apply, hgX] using ha
  have hle := trdeg_le_of_surjective g.rangeRestrict g.rangeRestrict_surjective
  rw [hA] at hle
  have hG : Algebra.trdeg K g.range = 1 := (Cardinal.le_one_iff.mp hle).resolve_left hnzero
  have hg' := surjective_algHom_injective_of_trdeg_eq g.rangeRestrict g.rangeRestrict_surjective
    (hA ▸ (by simp)) (hA.trans hG.symm)
  have hginj : Function.Injective g := by
    intro a b hab
    apply hg'
    exact Subtype.ext hab
  ext P
  change aeval y P = 0 ↔ aeval x P = 0
  constructor
  · intro hp
    have hq : Ideal.Quotient.mk I P = 0 := by
      apply hginj
      change aeval y P = g 0
      rw [map_zero]
      exact hp
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  · exact hrel P

/-- The actual generators of a generated field generate its whole
field also when regarded as elements of that field itself. -/
theorem fullOutputCoordinate_adjoin_eq_top (x : Fin n → F) :
    IntermediateField.adjoin K (Set.range (fullOutputCoordinate (K := K) x)) = ⊤ := by
  let M := fullOutputField (K := K) x
  apply IntermediateField.map_injective M.val
  have himage : M.val '' Set.range (fullOutputCoordinate (K := K) x) = Set.range x := by
    rw [← Set.range_comp]
    rfl
  have htop : (⊤ : IntermediateField K M).map M.val = M := by
    ext z
    constructor
    · rintro ⟨w, _, rfl⟩
      exact w.property
    · intro hz
      exact ⟨⟨z, hz⟩, trivial, rfl⟩
  rw [IntermediateField.adjoin_map, himage, htop]

/-- Nonconstant specialization of an actual curve constructs its
function-field embedding and carries every actual coordinate to its
specified specialized value. -/
theorem exists_curve_function_field_embedding_of_specialization
    (x : Fin n → F) (y : Fin n → E)
    (hdim : Algebra.trdeg K (fullOutputField (K := K) x) = 1)
    (hrel : ∀ P : MvPolynomial (Fin n) K, aeval x P = 0 → aeval y P = 0)
    (i : Fin n) (hy : Transcendental K (y i)) :
    ∃ f : fullOutputField (K := K) x →ₐ[K] E,
      ∀ j, f (fullOutputCoordinate (K := K) x j) = y j := by
  have heq := curve_coordinate_relations_equal_of_transcendental_specialization x y hdim hrel i hy
  have hrel' : fiberVanishingIdeal (L := K) y =
      fiberVanishingIdeal (L := K) (fullOutputCoordinate (K := K) x) := by
    rw [heq]
    ext P
    change aeval x P = 0 ↔ aeval (fullOutputCoordinate (K := K) x) P = 0
    have he : algebraMap (fullOutputField (K := K) x) F
        (aeval (fullOutputCoordinate (K := K) x) P) = 0 ↔
        aeval (fullOutputCoordinate (K := K) x) P = 0 :=
      map_eq_zero_iff (algebraMap (fullOutputField (K := K) x) F)
        (algebraMap (fullOutputField (K := K) x) F).injective
    rw [fullOutputCoordinate_aeval] at he
    exact he
  exact exists_fiber_embedding_of_relations_eq (fullOutputCoordinate (K := K) x) y
    (fullOutputCoordinate_adjoin_eq_top x) hrel'

end DimensionFourDependence
