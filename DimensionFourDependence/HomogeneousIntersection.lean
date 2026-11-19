import DimensionFourDependence.ProjectiveHilbert

/-! # The Hilbert-function identity for a two-equation intersection

Degree by degree, the coefficient map has precisely the Koszul relations.
Rank-nullity therefore gives the complete-intersection Hilbert identity.
-/

namespace DimensionFourDependence

open MvPolynomial Module

variable {L σ : Type*} [Field L]

/-- The coefficient map in a fixed homogeneous degree. -/
noncomputable def homogeneousPairMap
    (p q : MvPolynomial σ L) {dp dq : ℕ} (hp : p.IsHomogeneous dp) (hq : q.IsHomogeneous dq)
    (m : ℕ) :
    (homogeneousSubmodule σ L (dq + m)) × (homogeneousSubmodule σ L (dp + m)) →ₗ[L]
      homogeneousSubmodule σ L (dp + dq + m) where
  toFun z := ⟨p * (z.1 : MvPolynomial σ L) + q * (z.2 : MvPolynomial σ L), by
    apply IsHomogeneous.add
    · convert hp.mul z.1.property using 1; omega
    · convert hq.mul z.2.property using 1; omega⟩
  map_add' a b := by
    apply Subtype.ext
    change p * ((a.1 : MvPolynomial σ L) + b.1) + q * ((a.2 : MvPolynomial σ L) + b.2) = _
    simp only [mul_add, Submodule.coe_add]
    ring
  map_smul' a b := by
    apply Subtype.ext
    change p * (a • (b.1 : MvPolynomial σ L)) + q * (a • (b.2 : MvPolynomial σ L)) = _
    simp only [mul_smul_comm, smul_add, Submodule.coe_smul, RingHom.id_apply]

/-- The homogeneous Koszul relation in that degree. -/
noncomputable def homogeneousPairRelationMap
    (p q : MvPolynomial σ L) {dp dq : ℕ} (hp : p.IsHomogeneous dp) (hq : q.IsHomogeneous dq)
    (m : ℕ) : homogeneousSubmodule σ L m →ₗ[L]
      (homogeneousSubmodule σ L (dq + m)) × (homogeneousSubmodule σ L (dp + m)) where
  toFun c := (⟨q * (c : MvPolynomial σ L), hq.mul c.property⟩,
    ⟨-p * (c : MvPolynomial σ L), hp.neg.mul c.property⟩)
  map_add' a b := by
    apply Prod.ext <;> apply Subtype.ext <;> simp [mul_add]
  map_smul' a b := by
    apply Prod.ext <;> apply Subtype.ext <;> simp

theorem homogeneousPairRelationMap_injective
    (p q : MvPolynomial σ L) {dp dq : ℕ} (hp : p.IsHomogeneous dp) (hq : q.IsHomogeneous dq)
    (hp0 : p ≠ 0) (m : ℕ) : Function.Injective (homogeneousPairRelationMap p q hp hq m) := by
  intro a b hab
  apply Subtype.ext
  have he := congrArg (fun z : (homogeneousSubmodule σ L (dq + m)) ×
      (homogeneousSubmodule σ L (dp + m)) => (z.2 : MvPolynomial σ L)) hab
  exact mul_left_cancel₀ (neg_ne_zero.mpr hp0) he

/-- Exactness of the homogeneous Koszul complex at the coefficient space. -/
theorem homogeneousPair_exact
    (p q : MvPolynomial σ L) {dp dq : ℕ} (hp : p.IsHomogeneous dp) (hq : q.IsHomogeneous dq)
    (hp0 : p ≠ 0) (hcop : IsRelPrime p q) (m : ℕ) :
    LinearMap.range (homogeneousPairRelationMap p q hp hq m) =
      LinearMap.ker (homogeneousPairMap p q hp hq m) := by
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    apply Subtype.ext
    change p * (q * (c : MvPolynomial σ L)) + q * (-p * (c : MvPolynomial σ L)) = 0
    ring
  · intro hz
    have he : p * (z.1 : MvPolynomial σ L) + q * (z.2 : MvPolynomial σ L) = 0 :=
      congrArg Subtype.val hz
    obtain ⟨c, hc, ha, hb⟩ := relPrime_pair_homogeneous_syzygy p q hp0 hp hcop
      z.1 z.2 z.2.property he
    exact ⟨⟨c, hc⟩, Prod.ext (Subtype.ext ha.symm) (Subtype.ext hb.symm)⟩

/-- Every homogeneous element of the pair ideal has homogeneous coefficients
of the required degrees. -/
theorem homogeneousPair_range
    (p q : MvPolynomial σ L) {dp dq : ℕ} (hp : p.IsHomogeneous dp) (hq : q.IsHomogeneous dq)
    (m : ℕ) :
    LinearMap.range (homogeneousPairMap p q hp hq m) =
      homogeneousRelationSpace (Ideal.span ({p, q} : Set (MvPolynomial σ L))) (dp + dq + m) := by
  ext r
  constructor
  · rintro ⟨z, rfl⟩
    apply Ideal.mem_span_pair.mpr
    exact ⟨z.1, z.2, by change _ = p * (z.1 : MvPolynomial σ L) + q * (z.2 : MvPolynomial σ L); ring⟩
  · intro hr
    obtain ⟨a, b, he⟩ := Ideal.mem_span_pair.mp hr
    change a * p + b * q = (r : MvPolynomial σ L) at he
    have ha : homogeneousComponent (dp + dq + m) (a * p) = p * homogeneousComponent (dq + m) a := by
      rw [mul_comm a p, show dp + dq + m = (dq + m) + dp by omega]
      exact homogeneousComponent_mul_of_isHomogeneous hp a (dq + m)
    have hb : homogeneousComponent (dp + dq + m) (b * q) = q * homogeneousComponent (dp + m) b := by
      rw [mul_comm b q, show dp + dq + m = (dp + m) + dq by omega]
      exact homogeneousComponent_mul_of_isHomogeneous hq b (dp + m)
    have hv := congrArg (homogeneousComponent (dp + dq + m)) he
    rw [map_add, ha, hb, homogeneousComponent_of_mem r.property, ite_eq_left rfl] at hv
    exact ⟨(⟨homogeneousComponent (dq + m) a, homogeneousComponent_isHomogeneous _ _⟩,
      ⟨homogeneousComponent (dp + m) b, homogeneousComponent_isHomogeneous _ _⟩), Subtype.ext hv⟩

/-- The kernel has exactly the dimension of the shifted homogeneous polynomial space. -/
theorem homogeneousPair_kernel_finrank [Finite σ]
    (p q : MvPolynomial σ L) {dp dq : ℕ} (hp : p.IsHomogeneous dp) (hq : q.IsHomogeneous dq)
    (hp0 : p ≠ 0) (hcop : IsRelPrime p q) (m : ℕ) :
    finrank L (LinearMap.ker (homogeneousPairMap p q hp hq m)) =
      finrank L (homogeneousSubmodule σ L m) := by
  rw [← homogeneousPair_exact p q hp hq hp0 hcop m]
  exact LinearMap.finrank_range_of_inj (homogeneousPairRelationMap_injective p q hp hq hp0 m)

/-- The complete-intersection Hilbert identity, with no subtraction of natural dimensions. -/
theorem completeIntersection_hilbert_identity [Finite σ]
    (p q : MvPolynomial σ L) {dp dq : ℕ} (hp : p.IsHomogeneous dp) (hq : q.IsHomogeneous dq)
    (hp0 : p ≠ 0) (hcop : IsRelPrime p q) (m : ℕ) :
    projectiveHilbertFunction (Ideal.span ({p, q} : Set (MvPolynomial σ L))) (dp + dq + m) +
      finrank L (homogeneousSubmodule σ L (dq + m)) + finrank L (homogeneousSubmodule σ L (dp + m)) =
      finrank L (homogeneousSubmodule σ L (dp + dq + m)) + finrank L (homogeneousSubmodule σ L m) := by
  have hr := LinearMap.finrank_range_add_finrank_ker (homogeneousPairMap p q hp hq m)
  rw [homogeneousPair_range p q hp hq m, homogeneousPair_kernel_finrank p q hp hq hp0 hcop m,
    finrank_prod] at hr
  have hi := projectiveHilbertFunction_add_relation_finrank
    (Ideal.span ({p, q} : Set (MvPolynomial σ L))) (dp + dq + m)
  omega

end DimensionFourDependence
