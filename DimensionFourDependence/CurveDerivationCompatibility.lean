import DimensionFourDependence.ConstantField

/-! # Compatible derivations on a curve are determined by one transcendental parameter -/

namespace DimensionFourDependence

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {K J F : Type*} [Field K] [Field J] [Field F]
  [Algebra K J] [Algebra J F] [Algebra K F] [IsScalarTower K J F]

/-- Algebraic elements are annihilated also by field derivations
with values in a larger compatible field. -/
theorem module_derivation_zero_of_isAlgebraic [CharZero K]
    (δ : Derivation K J F) (a : J) (ha : IsAlgebraic K a) : δ a = 0 := by
  have hr := minpoly.aeval K a
  have hs := (minpoly.irreducible ha.isIntegral).separable
  have hn := hs.aeval_derivative_ne_zero hr
  have he := δ.map_aeval (minpoly K a) a
  rw [hr, map_zero] at he
  exact (smul_eq_zero.mp he.symm).resolve_left hn

/-- The kernel of a field-valued derivation is an actual subfield. -/
noncomputable def moduleDerivationConstants (δ : Derivation K J F) : IntermediateField K J where
  carrier := {a | δ a = 0}
  zero_mem' := map_zero δ
  one_mem' := δ.map_one_eq_zero
  add_mem' := by
    intro a b ha hb
    change δ a = 0 at ha
    change δ b = 0 at hb
    change δ (a + b) = 0
    rw [map_add, ha, hb, add_zero]
  mul_mem' := by
    intro a b ha hb
    change δ (a * b) = 0
    rw [δ.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
  algebraMap_mem' := δ.map_algebraMap
  inv_mem' := by
    intro a ha
    change δ a⁻¹ = 0
    rw [δ.leibniz_inv, ha, smul_zero]

/-- Changing to a larger constant base leaves every actual
field-valued derivation value unchanged. -/
noncomputable def moduleDerivationOverConstantSubfield (δ : Derivation K J F)
    (B : IntermediateField K J) (hB : B ≤ moduleDerivationConstants δ) :
    Derivation B J F where
  toLinearMap :=
    { toFun := δ
      map_add' := map_add δ
      map_smul' := by
        intro c a
        simp only [RingHom.id_apply, Algebra.smul_def]
        change δ ((c : J) * a) = algebraMap B F c * δ a
        rw [δ.leibniz, show δ (c : J) = 0 from hB c.property, smul_zero, add_zero]
        simp only [Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply B J F, IntermediateField.algebraMap_apply] }
  map_one_eq_zero' := δ.map_one_eq_zero
  leibniz' := δ.leibniz

/-- On a curve field, agreement at a transcendental parameter
forces full compatibility of the source derivation and an ambient
derivation, with values in the actual ambient field. -/
theorem curve_derivation_compatible_of_parameter [CharZero K]
    (D : Derivation K J J) (Δ : Derivation K F F)
    (t : J) (ht : Transcendental K t) (hJ : Algebra.trdeg K J ≤ 1)
    (hparam : Δ (algebraMap J F t) = algebraMap J F (D t)) :
    ∀ a : J, Δ (algebraMap J F a) = algebraMap J F (D a) := by
  let δ : Derivation K J F := Δ.compAlgebraMap J - (Algebra.linearMap J F).compDer D
  let B := IntermediateField.adjoin K {t}
  have hB : B ≤ moduleDerivationConstants δ := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro a ha
    have ha' : a = t := Set.mem_singleton_iff.mp ha
    subst a
    change Δ (algebraMap J F t) - algebraMap J F (D t) = 0
    exact sub_eq_zero.mpr hparam
  let δB := moduleDerivationOverConstantSubfield δ B hB
  letI : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  intro a
  have hz := module_derivation_zero_of_isAlgebraic δB a
    (isAlgebraic_over_adjoin_of_trdeg_le_one hJ t ht a)
  change Δ (algebraMap J F a) - algebraMap J F (D a) = 0 at hz
  exact sub_eq_zero.mp hz

/-- The constants of a nonzero derivation of a curve over an
algebraically closed original field are exactly original constants. -/
theorem curve_derivation_constants_are_original [CharZero K] [IsAlgClosed K]
    (D : Derivation K J J) (hD : D ≠ 0) (hJ : Algebra.trdeg K J ≤ 1)
    (a : J) (ha : D a = 0) : ∃ c : K, algebraMap K J c = a := by
  have halg := (derivation_zero_iff_isAlgebraic_of_trdeg_le_one D hD hJ a).mp ha
  let B := IntermediateField.adjoin K {a}
  letI : Algebra.IsAlgebraic K B := IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
  letI : Algebra.IsIntegral K B := ⟨fun x => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral⟩
  let b : B := ⟨a, IntermediateField.subset_adjoin K {a} (Set.mem_singleton a)⟩
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B)).surjective b
  refine ⟨c, ?_⟩
  exact (IsScalarTower.algebraMap_apply K B J c).trans (congrArg (algebraMap B J) hc)

end DimensionFourDependence
