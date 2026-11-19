import DimensionFourDependence.AmbientDerivation

/-! # The chain rule on the algebraic coefficient field of Lemma 2.2 -/

namespace DimensionFourDependence

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

omit [CharZero K] in
/-- A derivation on an output field vanishes if it kills its generators. -/
theorem ambient_derivation_adjoin_zero (Y : Fin n → F)
    (D : Derivation K (IntermediateField.adjoin K (Set.range Y)) F)
    (hY : ∀ i, D (outputCoordinate (K := K) Y i) = 0)
    (a : IntermediateField.adjoin K (Set.range Y)) : D a = 0 := by
  rcases a with ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩
    exact hY i
  | algebraMap a => exact D.map_algebraMap a
  | add x y hx hy ihx ihy =>
    change D ((⟨x, hx⟩ : IntermediateField.adjoin K (Set.range Y)) + ⟨y, hy⟩) = 0
    rw [map_add, ihx, ihy, add_zero]
  | inv x hx ih =>
    change D ((⟨x, hx⟩ : IntermediateField.adjoin K (Set.range Y))⁻¹) = 0
    rw [D.leibniz_inv, ih, smul_zero]
  | mul x y hx hy ihx ihy =>
    change D ((⟨x, hx⟩ : IntermediateField.adjoin K (Set.range Y)) * ⟨y, hy⟩) = 0
    rw [D.leibniz, ihx, ihy, smul_zero, smul_zero, add_zero]

omit [CharZero K] in
/-- The scalar tower from the ground field through the relative closure. -/
theorem coefficientFieldScalarTower (Y : Fin n → F) :
    IsScalarTower K (coefficientField (K := K) Y) F :=
  IsScalarTower.to₁₃₄ K (IntermediateField.adjoin K (Set.range Y))
    (coefficientField (K := K) Y) F

attribute [local instance] coefficientFieldScalarTower

/-- View a coefficient-coordinate derivative as taking values in the
ambient source field. -/
noncomputable def coefficientAmbientPartial (Y : Fin n → F)
    (hY : AlgebraicIndependent K Y) (i : Fin n) :
    Derivation K (coefficientField (K := K) Y) F :=
  (Algebra.linearMap (coefficientField (K := K) Y) F).compDer
    (coefficientPartial (K := K) Y hY i)

theorem coefficientAmbientPartial_apply (Y : Fin n → F)
    (hY : AlgebraicIndependent K Y) (i : Fin n) (a : coefficientField (K := K) Y) :
    coefficientAmbientPartial Y hY i a = (coefficientPartial (K := K) Y hY i a : F) := rfl

/-- Ambient-valued derivations on `L` are determined by their values on `Y`. -/
theorem coefficient_ambient_derivation_ext (Y : Fin n → F)
    (D₁ D₂ : Derivation K (coefficientField (K := K) Y) F)
    (hY : ∀ j, D₁ (algebraMap (IntermediateField.adjoin K (Set.range Y))
        (coefficientField (K := K) Y) (outputCoordinate (K := K) Y j)) =
      D₂ (algebraMap (IntermediateField.adjoin K (Set.range Y))
        (coefficientField (K := K) Y) (outputCoordinate (K := K) Y j))) : D₁ = D₂ := by
  apply ambient_derivation_extension_unique
    (E := IntermediateField.adjoin K (Set.range Y)) D₁ D₂
  · intro a
    have hz := ambient_derivation_adjoin_zero Y
      ((D₁ - D₂).compAlgebraMap (IntermediateField.adjoin K (Set.range Y)))
      (fun j => by simpa using sub_eq_zero.mpr (hY j)) a
    exact sub_eq_zero.mp hz
  · exact Algebra.IsAlgebraic.isAlgebraic

/-- The chain rule for every algebraic coefficient in the actual source
field, without requiring its source derivatives to belong to `L`. -/
theorem coefficient_chain_rule (Y : Fin n → F) (hY : AlgebraicIndependent K Y)
    (D : Derivation K F F) (a : coefficientField (K := K) Y) :
    D (a : F) = ∑ i : Fin n, D (Y i) * (coefficientPartial (K := K) Y hY i a : F) := by
  let Δ : Derivation K (coefficientField (K := K) Y) F :=
    ∑ i : Fin n, D (Y i) • coefficientAmbientPartial Y hY i
  have heq : D.compAlgebraMap (coefficientField (K := K) Y) = Δ := by
    apply coefficient_ambient_derivation_ext Y
    intro j
    change D (Y j) = Δ _
    simp only [Δ, sum_apply, Derivation.smul_apply,
      coefficientAmbientPartial_apply, coefficientPartial_coordinate]
    simp [apply_ite, smul_eq_mul]
  have h := congrArg (fun d : Derivation K (coefficientField (K := K) Y) F => d a) heq
  simpa only [Derivation.compAlgebraMap_apply, Δ, sum_apply,
    Derivation.smul_apply, coefficientAmbientPartial_apply, smul_eq_mul,
    IntermediateField.algebraMap_apply] using h

end DimensionFourDependence
