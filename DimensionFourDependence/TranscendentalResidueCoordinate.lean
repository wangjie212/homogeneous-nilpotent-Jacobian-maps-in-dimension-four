import DimensionFourDependence.Defs

/-! # A nonclosed divisor has a transcendental original residue coordinate

If all images of algebra generators in a residue field are algebraic,
their full coordinate quotient is integral over the ground field and
therefore is a field. Thus a nonmaximal contraction forces one of the
original coordinate residues to be transcendental. The same conclusion
holds under an integral normalization extension.
-/

namespace DimensionFourDependence

variable {k A F σ : Type*} [Field k] [CommRing A] [Algebra k A]
  [Field F] [Algebra k F]

/-- If all original algebra generators have algebraic images in a field,
the kernel of that field-valued map is maximal. -/
theorem kernel_isMaximal_of_algebraic_coordinates
    (x : σ → A) (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (g : A →ₐ[k] F) (halg : ∀ i, IsAlgebraic k (g (x i))) :
    (RingHom.ker g).IsMaximal := by
  let S := (Subalgebra.algebraicClosure k F).comap g
  have hle : Algebra.adjoin k (Set.range x) ≤ S := by
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact halg i
  have hall (a : A) : IsAlgebraic k (g a) := by
    apply hle
    rw [hx]
    trivial
  let e := Ideal.kerLiftAlg g
  letI : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  letI : Algebra.IsIntegral k (A ⧸ RingHom.ker g) := ⟨fun a => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply (isIntegral_algHom_iff e (Ideal.kerLiftAlg_injective g)).mp
    exact (hall b).isIntegral⟩
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr
    (isField_of_isIntegral_of_isField' (R := k) (S := A ⧸ RingHom.ker g)
      (inferInstance : Field k).toIsField)

variable {B : Type*} [CommRing B] [IsLocalRing B] [Algebra A B]
  [Algebra k B] [IsScalarTower k A B]

/-- A nonmaximal original coordinate contraction forces an actual
transcendental coordinate in the local residue field. -/
theorem exists_transcendental_residue_coordinate_of_not_isMaximal
    (x : σ → A) (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (hnot : ¬ ((IsLocalRing.maximalIdeal B).under A).IsMaximal) :
    ∃ i, Transcendental k (IsLocalRing.residue B (algebraMap A B (x i))) := by
  by_contra! h
  let g : A →ₐ[k] IsLocalRing.ResidueField B :=
    (IsScalarTower.toAlgHom k B (IsLocalRing.ResidueField B)).comp
      (IsScalarTower.toAlgHom k A B)
  have hm := kernel_isMaximal_of_algebraic_coordinates x hx g (fun i => by
    change IsAlgebraic k (algebraMap B (IsLocalRing.ResidueField B) (algebraMap A B (x i)))
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact not_not.mp (h i))
  apply hnot
  have hker : RingHom.ker g = (IsLocalRing.maximalIdeal B).under A := by
    ext a
    exact IsLocalRing.residue_eq_zero_iff _
  rwa [← hker]

variable {S : Type*} [CommRing S] [Algebra A S] [Algebra.IsIntegral A S]
  [Algebra S B] [IsScalarTower A S B]

/-- Passing to an integral normalization does not destroy the existence
of a transcendental original coordinate at a nonmaximal local center. -/
theorem exists_transcendental_residue_coordinate_of_integral_extension
    (x : σ → A) (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (hnot : ¬ ((IsLocalRing.maximalIdeal B).under S).IsMaximal) :
    ∃ i, Transcendental k (IsLocalRing.residue B (algebraMap A B (x i))) := by
  apply exists_transcendental_residue_coordinate_of_not_isMaximal x hx
  intro hm
  apply hnot
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A)
  rwa [Ideal.under_under]

end DimensionFourDependence
