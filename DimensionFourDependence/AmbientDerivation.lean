import DimensionFourDependence.CoefficientField

/-! # Algebraic uniqueness for derivations with values in an ambient field

The source-coordinate derivatives of an algebraic coefficient need not lie
in the coefficient field. These results allow the codomain to be the larger
source field, as required by the chain rule in Lemma 2.2.
-/

namespace DimensionFourDependence

variable {K L F : Type*} [Field K] [Field L] [Field F]
  [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]

/-- The kernel of an ambient-valued derivation is still a field. -/
noncomputable def ambientDerivationConstants (D : Derivation K L F) : IntermediateField K L where
  carrier := {x | D x = 0}
  zero_mem' := map_zero D
  one_mem' := D.map_one_eq_zero
  add_mem' := by
    intro x y hx hy
    change D (x + y) = 0
    rw [map_add, hx, hy, add_zero]
  mul_mem' := by
    intro x y hx hy
    change D (x * y) = 0
    rw [D.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  algebraMap_mem' := D.map_algebraMap
  inv_mem' := by
    intro x hx
    change D x⁻¹ = 0
    rw [D.leibniz_inv, hx, smul_zero]

omit [IsScalarTower K L F] in
/-- A separable algebraic element is annihilated even when the values of
the derivation lie in a larger field. -/
theorem ambient_derivation_zero_of_isAlgebraic [CharZero K]
    (D : Derivation K L F) (x : L) (hx : IsAlgebraic K x) : D x = 0 := by
  have hr := minpoly.aeval K x
  have hsep := (minpoly.irreducible hx.isIntegral).separable
  have hne := hsep.aeval_derivative_ne_zero hr
  have h := D.map_aeval (minpoly K x) x
  rw [hr, map_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hne

variable {E : Type*} [Field E] [Algebra K E] [Algebra E L] [Algebra E F]
  [IsScalarTower K E L] [IsScalarTower K E F] [IsScalarTower E L F]

/-- Change the base field of an ambient-valued derivation that kills it. -/
noncomputable def ambientDerivationChangeBase (D : Derivation K L F)
    (hE : ∀ a : E, D (algebraMap E L a) = 0) : Derivation E L F where
  toLinearMap :=
    { toFun := D
      map_add' := map_add D
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [D.leibniz, hE, smul_zero, add_zero]
        simp only [Algebra.smul_def, ← IsScalarTower.algebraMap_apply E L F] }
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

omit [IsScalarTower K L F] [Algebra K E] [IsScalarTower K E L] [IsScalarTower K E F] in
/-- Uniqueness on algebraic extensions with an ambient field as codomain. -/
theorem ambient_derivation_extension_unique [CharZero E]
    (D₁ D₂ : Derivation K L F)
    (hE : ∀ a : E, D₁ (algebraMap E L a) = D₂ (algebraMap E L a))
    (hAlg : ∀ x : L, IsAlgebraic E x) : D₁ = D₂ := by
  apply sub_eq_zero.mp
  ext x
  exact ambient_derivation_zero_of_isAlgebraic (K := E)
    (ambientDerivationChangeBase (E := E) (D₁ - D₂)
      (fun a => by simp only [Derivation.sub_apply, hE, sub_self])) x (hAlg x)

end DimensionFourDependence
