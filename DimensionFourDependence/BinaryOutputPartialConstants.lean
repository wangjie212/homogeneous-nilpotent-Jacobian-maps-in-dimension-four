import DimensionFourDependence.CoefficientEuler
import DimensionFourDependence.RationalJacobianCriterion

/-! # Constants of one output partial are algebraic over the other output -/

namespace DimensionFourDependence

universe u
set_option maxHeartbeats 1850000

variable {K F : Type u} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

omit [CharZero K] in
/-- The absolute transcendence degree of the actual coefficient field
is the number of independent output coordinates. -/
theorem coefficientField_trdeg_eq_independent_output_count
    (Y : Fin n → F) (hY : AlgebraicIndependent K Y) :
    Algebra.trdeg K (coefficientField (K := K) Y) = n := by
  let B := IntermediateField.adjoin K (Set.range Y)
  let L := coefficientField (K := K) Y
  let : IsScalarTower K B L := IsScalarTower.of_algebraMap_eq (by intro k; rfl)
  let : FaithfulSMul K B :=
    (faithfulSMul_iff_algebraMap_injective K B).mpr (algebraMap K B).injective
  let : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr (algebraMap B L).injective
  have he := (rationalOutputEquiv Y hY).trdeg_eq
  rw [rationalSource_trdeg_eq] at he
  have h := trdeg_add_eq (A := L) K B
  rw [show Algebra.trdeg B L = 0 from trdeg_eq_zero, add_zero, ← he] at h
  exact h.symm

/-- An element killed by the second independent output partial is
algebraic over the first output, in the original ambient source field. -/
theorem second_coefficientPartial_zero_isAlgebraic_over_first_output
    (Y : Fin 2 → F) (hY : AlgebraicIndependent K Y)
    (a : coefficientField (K := K) Y) (ha : coefficientPartial Y hY 1 a = 0) :
    IsAlgebraic (IntermediateField.adjoin K {Y 0}) (a : F) := by
  let L := coefficientField (K := K) Y
  let : IsScalarTower K L F := coefficientFieldScalarTower Y
  let y := coefficientCoordinate (K := K) Y 0
  let D := coefficientPartial Y hY 1
  let E := IntermediateField.adjoin K ({y} : Set L)
  have hcoord (i : Fin 2) : D (coefficientCoordinate (K := K) Y i) = if i = 1 then 1 else 0 :=
    coefficientPartial_coordinate Y hY 1 i
  have hy : D y = 0 := by
    simpa only [show (0 : Fin 2) ≠ 1 by decide, ite_false] using hcoord 0
  have hE : E ≤ derivationConstants D :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hy)
  let d := derivationOverConstantSubfield D E hE
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hd : d ≠ 0 := by
    intro h
    have he := congrArg (fun g : Derivation E L L => g (coefficientCoordinate (K := K) Y 1)) h
    change D (coefficientCoordinate (K := K) Y 1) = 0 at he
    rw [hcoord, if_pos rfl] at he
    exact one_ne_zero he
  let f : L →ₐ[K] F := IsScalarTower.toAlgHom K L F
  have hY₀ : AlgebraicIndependent K (fun _ : Fin 1 => y) := by
    apply algebraicIndependent_unique_type_iff.mpr
    intro hyAlg
    exact hY.transcendental 0 (hyAlg.algHom f)
  have hRange : Set.range (fun _ : Fin 1 => y) = {y} := by ext z; simp
  have ht : Algebra.trdeg E L ≤ 1 := by
    change Algebra.trdeg (IntermediateField.adjoin K ({y} : Set L)) L ≤ 1
    rw [← hRange]
    apply relative_trdeg_le_one_of_independent_outputs _ hY₀
    rw [coefficientField_trdeg_eq_independent_output_count Y hY]
    norm_num
  have hAlg : IsAlgebraic E a := (derivation_zero_iff_isAlgebraic_of_trdeg_le_one d hd ht a).mp ha
  let e := IntermediateField.equivMap E f
  have hCompat : (algebraMap (E.map f) F).comp e.toRingHom =
      f.toRingHom.comp (algebraMap E L) := by
    ext a
    rfl
  have hmap : E.map f = IntermediateField.adjoin K {Y 0} := by
    change (IntermediateField.adjoin K {y}).map f = _
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  rw [← hmap]
  exact (isAlgebraic_ringHom_iff_of_comp_eq e.toRingEquiv f.toRingHom f.injective hCompat).mpr hAlg

end DimensionFourDependence
