import DimensionFourDependence.SmallIntersectionHilbert

/-! # Hilbert recurrence for multiplication by a coordinate

The kernel is described by a colon ideal and the cokernel by adding the
coordinate to the relations. All three spaces use the actual graded quotient.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {L σ : Type*} [Field L]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ideal quotient by a single coordinate. -/
noncomputable def coordinateColon (I : Ideal (MvPolynomial σ L)) (i : σ) :
    Ideal (MvPolynomial σ L) := I.colon {X i}

theorem le_coordinateColon (I : Ideal (MvPolynomial σ L)) (i : σ) :
    I ≤ coordinateColon I i := by
  intro p hp
  apply Submodule.mem_colon_singleton.mpr
  exact I.mul_mem_right (X i) hp

/-- Multiplication by a coordinate between consecutive homogeneous pieces. -/
noncomputable def homogeneousCoordinateMap (i : σ) (d : ℕ) :
    homogeneousSubmodule σ L d →ₗ[L] homogeneousSubmodule σ L (d + 1) where
  toFun p := ⟨X i * (p : MvPolynomial σ L), by
    change (X i * (p : MvPolynomial σ L)).IsHomogeneous (d + 1)
    simpa only [Nat.add_comm] using (isHomogeneous_X (R := L) i).mul p.property⟩
  map_add' p q := by apply Subtype.ext; simp [mul_add]
  map_smul' a p := by apply Subtype.ext; simp

theorem homogeneousCoordinateMap_injective (i : σ) (d : ℕ) :
    Function.Injective (homogeneousCoordinateMap (L := L) i d) := by
  intro p q hpq
  exact Subtype.ext (mul_left_cancel₀ (X_ne_zero i) (congrArg Subtype.val hpq))

/-- Homogeneity is preserved by taking an ideal quotient by a coordinate. -/
theorem coordinateColon_isHomogeneous (I : Ideal (MvPolynomial σ L))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ L)) (i : σ) :
    (coordinateColon I i).IsHomogeneous (homogeneousSubmodule σ L) := by
  intro d p hp
  change (MvPolynomial.decomposition.decompose' p d : MvPolynomial σ L) ∈ coordinateColon I i
  rw [MvPolynomial.decomposition.decompose'_apply]
  apply Submodule.mem_colon_singleton.mpr
  have hx : X i * p ∈ I := by
    simpa only [smul_eq_mul, mul_comm] using Submodule.mem_colon_singleton.mp hp
  have hc := homogeneousComponent_mem_of_mem hI hx (d + 1)
  rw [homogeneousComponent_mul_of_isHomogeneous (isHomogeneous_X (R := L) i) p d] at hc
  simpa only [smul_eq_mul, mul_comm] using hc

theorem sup_coordinate_isHomogeneous (I : Ideal (MvPolynomial σ L))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ L)) (i : σ) :
    (I ⊔ Ideal.span ({X i} : Set (MvPolynomial σ L))).IsHomogeneous (homogeneousSubmodule σ L) := by
  apply hI.sup
  apply Ideal.homogeneous_span
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact ⟨1, isHomogeneous_X (R := L) i⟩

/-- The preimage of the relation space is the colon ideal's relation space. -/
theorem homogeneousCoordinateMap_relation_comap (I : Ideal (MvPolynomial σ L)) (i : σ) (d : ℕ) :
    (homogeneousRelationSpace I (d + 1)).comap (homogeneousCoordinateMap i d) =
      homogeneousRelationSpace (coordinateColon I i) d := by
  ext p
  change X i * (p : MvPolynomial σ L) ∈ I ↔ (p : MvPolynomial σ L) ∈ coordinateColon I i
  rw [coordinateColon, Submodule.mem_colon_singleton]
  simp only [smul_eq_mul, mul_comm]

/-- Adding a coordinate adds exactly the image of multiplication by it
to each homogeneous relation space. -/
theorem homogeneousCoordinateMap_relation_sup (I : Ideal (MvPolynomial σ L))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ L)) (i : σ) (d : ℕ) :
    homogeneousRelationSpace (I ⊔ Ideal.span ({X i} : Set (MvPolynomial σ L))) (d + 1) =
      LinearMap.range (homogeneousCoordinateMap i d) ⊔ homogeneousRelationSpace I (d + 1) := by
  ext r
  constructor
  · intro hr
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hr
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
    change a + b = (r : MvPolynomial σ L) at he
    rw [hc] at he
    have hv := congrArg (homogeneousComponent (d + 1)) he
    rw [map_add, homogeneousComponent_mul_of_isHomogeneous (isHomogeneous_X (R := L) i) c d,
      homogeneousComponent_of_mem r.property, ite_eq_left rfl] at hv
    apply Submodule.mem_sup.mpr
    refine ⟨homogeneousCoordinateMap i d ⟨homogeneousComponent d c, homogeneousComponent_isHomogeneous _ _⟩,
      ⟨_, rfl⟩, ⟨homogeneousComponent (d + 1) a, homogeneousComponent_isHomogeneous _ _⟩,
      homogeneousComponent_mem_of_mem hI ha (d + 1), ?_⟩
    apply Subtype.ext
    change X i * homogeneousComponent d c + homogeneousComponent (d + 1) a = (r : MvPolynomial σ L)
    simpa only [add_comm] using hv
  · intro hr
    obtain ⟨a, ⟨p, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.mp hr
    change X i * (p : MvPolynomial σ L) + (b : MvPolynomial σ L) ∈ I ⊔ Ideal.span {X i}
    apply (I ⊔ Ideal.span {X i}).add_mem
    · exact (show Ideal.span {X i} ≤ I ⊔ Ideal.span {X i} from le_sup_right)
        (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _))
    · exact (show I ≤ I ⊔ Ideal.span {X i} from le_sup_left) hb

/-- The Hilbert recurrence for a coordinate, proved by finite-dimensional
rank identities rather than by assuming a Hilbert polynomial exists. -/
theorem projectiveHilbertFunction_coordinate_recurrence [Finite σ]
    (I : Ideal (MvPolynomial σ L)) (hI : I.IsHomogeneous (homogeneousSubmodule σ L)) (i : σ) (d : ℕ) :
    projectiveHilbertFunction I (d + 1) = projectiveHilbertFunction (coordinateColon I i) d +
      projectiveHilbertFunction (I ⊔ Ideal.span ({X i} : Set (MvPolynomial σ L))) (d + 1) := by
  let f := homogeneousCoordinateMap (L := L) i d
  let U := LinearMap.range f
  let V := homogeneousRelationSpace I (d + 1)
  have hf : Function.Injective f := homogeneousCoordinateMap_injective i d
  have hU : finrank L U = finrank L (homogeneousSubmodule σ L d) := LinearMap.finrank_range_of_inj hf
  have hc : (U ⊓ V).comap f = homogeneousRelationSpace (coordinateColon I i) d := by
    ext p
    change (f p ∈ U ∧ f p ∈ V) ↔ _
    simp only [show f p ∈ U from ⟨p, rfl⟩, true_and]
    exact SetLike.ext_iff.mp (homogeneousCoordinateMap_relation_comap I i d) p
  have hUV : finrank L ↥(U ⊓ V) = finrank L (homogeneousRelationSpace (coordinateColon I i) d) := by
    rw [← hc]
    exact (Submodule.comap_equiv_self_of_inj_of_le hf (show U ⊓ V ≤ LinearMap.range f from inf_le_left)).finrank_eq.symm
  have hs := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hU, hUV] at hs
  have hsup : U ⊔ V = homogeneousRelationSpace (I ⊔ Ideal.span ({X i} : Set (MvPolynomial σ L))) (d + 1) :=
    (homogeneousCoordinateMap_relation_sup I hI i d).symm
  rw [hsup] at hs
  change finrank L (homogeneousRelationSpace (I ⊔ Ideal.span ({X i} : Set (MvPolynomial σ L))) (d + 1)) +
    finrank L (homogeneousRelationSpace (coordinateColon I i) d) =
      finrank L (homogeneousSubmodule σ L d) + finrank L (homogeneousRelationSpace I (d + 1)) at hs
  have h1 := projectiveHilbertFunction_add_relation_finrank I (d + 1)
  have h2 := projectiveHilbertFunction_add_relation_finrank (coordinateColon I i) d
  have h3 := projectiveHilbertFunction_add_relation_finrank
    (I ⊔ Ideal.span ({X i} : Set (MvPolynomial σ L))) (d + 1)
  omega

end DimensionFourDependence
