import DimensionFourDependence.NormalizationRing

/-! # Algebraic generation of residue fraction fields by original coordinates -/

namespace DimensionFourDependence

variable {E J A B L σ : Type*} [Field E] [Field J] [CommRing A] [CommRing B]
  [Field L] [Algebra E A] [Algebra E L] [Algebra A L] [IsScalarTower E A L]
  [Algebra J L]

/-- Images of algebra generators and coefficients that are algebraic
over a field force every image of the original algebra to be algebraic. -/
theorem algebraic_image_of_algebraic_coordinates
    (x : σ → A) (hgen : Algebra.adjoin E (Set.range x) = ⊤)
    (hcoeff : ∀ e : E, IsAlgebraic J (algebraMap E L e))
    (hcoord : ∀ i, IsAlgebraic J (algebraMap A L (x i))) :
    ∀ a : A, IsAlgebraic J (algebraMap A L a) := by
  let S : Subalgebra E L :=
    { (Subalgebra.algebraicClosure J L).toSubring with algebraMap_mem' := hcoeff }
  let g := IsScalarTower.toAlgHom E A L
  have hle : Algebra.adjoin E (Set.range x) ≤ S.comap g := by
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact hcoord i
  intro a
  apply hle
  rw [hgen]
  trivial

variable [Algebra A B] [Algebra.IsIntegral A B]
  [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]

include B in
/-- The fraction field of an integral coordinate extension is algebraic
over any field over which its original coefficients and coordinate
values are algebraic. No algebra structure from that field on the
original coordinate ring is required. -/
theorem integral_coordinate_fraction_field_isAlgebraic
    (x : σ → A) (hgen : Algebra.adjoin E (Set.range x) = ⊤)
    (hcoeff : ∀ e : E, IsAlgebraic J (algebraMap E L e))
    (hcoord : ∀ i, IsAlgebraic J (algebraMap A L (x i))) :
    Algebra.IsAlgebraic J L := by
  let C := algebraicClosure J L
  have hA := algebraic_image_of_algebraic_coordinates x hgen hcoeff hcoord
  let f : A →+* C :=
    { toFun := fun a => ⟨algebraMap A L a, mem_algebraicClosure_iff.mpr (hA a)⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) }
  have hcomp : (algebraMap C L).comp f = (algebraMap B L).comp (algebraMap A B) := by
    ext a
    exact IsScalarTower.algebraMap_apply A B L a
  have hB (b : B) : algebraMap B L b ∈ C := by
    apply mem_algebraicClosure_iff.mpr
    exact ((Algebra.IsIntegral.isIntegral (R := A) b).map_of_comp_eq f
      (algebraMap B L) hcomp).trans_isAlgebraic (R := J)
  constructor
  intro z
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective B z
  exact mem_algebraicClosure_iff.mp (C.div_mem (hB a) (hB b))

end DimensionFourDependence
