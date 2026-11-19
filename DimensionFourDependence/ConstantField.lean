import DimensionFourDependence.Flag

/-! # Constants of a derivation in relative transcendence degree one

This is the field-theoretic constant-field assertion in the proof of
Lemma 2.2. The field `K` in this module plays the role of the output field
`K(Y)` in the paper; the ambient field plays the role of `K(X)`.
-/

namespace DimensionFourDependence

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Elements annihilated by a derivation form an intermediate field. -/
noncomputable def derivationConstants (D : Derivation K F F) : IntermediateField K F where
  carrier := {x | D x = 0}
  zero_mem' := map_zero D
  one_mem' := D.map_one_eq_zero
  add_mem' := by
    intro x y hx hy
    change D x = 0 at hx
    change D y = 0 at hy
    change D (x + y) = 0
    rw [map_add, hx, hy, add_zero]
  mul_mem' := by
    intro x y hx hy
    change D x = 0 at hx
    change D y = 0 at hy
    change D (x * y) = 0
    rw [D.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  algebraMap_mem' := D.map_algebraMap
  inv_mem' := by
    intro x hx
    change D x = 0 at hx
    change D x⁻¹ = 0
    rw [D.leibniz_inv, hx, smul_zero]

theorem mem_derivationConstants (D : Derivation K F F) (x : F) :
    x ∈ derivationConstants D ↔ D x = 0 := Iff.rfl

/-- A characteristic-zero algebraic element is killed by every derivation
over the base field, by differentiating its separable minimal polynomial. -/
theorem derivation_zero_of_isAlgebraic [CharZero K]
    (D : Derivation K F F) (x : F) (hx : IsAlgebraic K x) : D x = 0 := by
  have hr := minpoly.aeval K x
  have hsep := (minpoly.irreducible hx.isIntegral).separable
  have hne := hsep.aeval_derivative_ne_zero hr
  have h := D.map_aeval (minpoly K x) x
  rw [hr, map_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hne

/-- Restricting the base of a derivation to any intermediate field of
constants leaves the same underlying function. -/
noncomputable def derivationOverConstantSubfield (D : Derivation K F F)
    (E : IntermediateField K F) (hE : E ≤ derivationConstants D) : Derivation E F F where
  toLinearMap :=
    { toFun := D
      map_add' := map_add D
      map_smul' := by
        intro c y
        change D ((c : F) * y) = (c : F) * D y
        rw [D.leibniz, show D (c : F) = 0 from hE c.property]
        simp [smul_eq_mul] }
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

theorem derivationOverConstantSubfield_apply (D : Derivation K F F)
    (E : IntermediateField K F) (hE : E ≤ derivationConstants D) (x : F) :
    derivationOverConstantSubfield D E hE x = D x := rfl

/-- A transcendental element generates an algebraic extension when the
ambient relative transcendence degree is at most one. -/
theorem isAlgebraic_over_adjoin_of_trdeg_le_one
    (htr : Algebra.trdeg K F ≤ 1) (x : F) (hx : Transcendental K x) (y : F) :
    IsAlgebraic (IntermediateField.adjoin K {x}) y := by
  have hi : AlgebraicIndependent K (fun _ : Fin 1 => x) := by
    simpa using hx
  have hb := hi.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by simpa using htr)
  have ha := hb.isAlgebraic.isAlgebraic y
  have hr : Set.range (fun _ : Fin 1 => x) = {x} := by ext z; simp
  rw [hr] at ha
  exact IntermediateField.isAlgebraic_adjoin_iff.mpr ha

/-- The constants in a one-dimensional function-field extension are exactly
the elements algebraic over the base field, as used in Lemma 2.2. -/
theorem derivation_zero_iff_isAlgebraic_of_trdeg_le_one [CharZero K]
    (D : Derivation K F F) (hD : D ≠ 0) (htr : Algebra.trdeg K F ≤ 1) (x : F) :
    D x = 0 ↔ IsAlgebraic K x := by
  constructor
  · intro hDx
    by_contra hxa
    have hx : Transcendental K x := hxa
    let E := IntermediateField.adjoin K ({x} : Set F)
    have hE : E ≤ derivationConstants D := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro z hz
      have hz' : z = x := Set.mem_singleton_iff.mp hz
      subst z
      exact hDx
    let d := derivationOverConstantSubfield D E hE
    have hd : ∀ y : F, d y = 0 := by
      intro y
      apply derivation_zero_of_isAlgebraic d y
      exact isAlgebraic_over_adjoin_of_trdeg_le_one htr x hx y
    apply hD
    ext y
    exact hd y
  · exact derivation_zero_of_isAlgebraic D x

/-- Equality of intermediate fields, not just a pointwise description of
the constants. This is the constant-field assertion in Lemma 2.2. -/
theorem derivationConstants_eq_relativeAlgebraicClosure [CharZero K]
    (D : Derivation K F F) (hD : D ≠ 0) (htr : Algebra.trdeg K F ≤ 1) :
    derivationConstants D = algebraicClosure K F := by
  ext x
  exact (derivation_zero_iff_isAlgebraic_of_trdeg_le_one D hD htr x).trans
    mem_algebraicClosure_iff.symm

end DimensionFourDependence
