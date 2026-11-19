import DimensionFourDependence.ProjectiveFiberEquations

/-! # Relative dimension of the generic fiber function field

Passing from `K(Y)` to its actual relative algebraic closure does not
change the relative transcendence degree. A nonzero vertical derivation
then proves that the degree is exactly one.
-/

namespace DimensionFourDependence

open Matrix

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

omit [CharZero K] in
/-- The algebraic coefficient-field extension leaves the relative
transcendence degree unchanged. -/
theorem coefficientField_trdeg_eq_output_trdeg (Y : Fin n → F) :
    Algebra.trdeg (coefficientField (K := K) Y) F =
      Algebra.trdeg (IntermediateField.adjoin K (Set.range Y)) F := by
  let : FaithfulSMul (IntermediateField.adjoin K (Set.range Y)) (coefficientField (K := K) Y) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap (IntermediateField.adjoin K (Set.range Y)) (coefficientField (K := K) Y)).injective
  let : FaithfulSMul (coefficientField (K := K) Y) F :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap (coefficientField (K := K) Y) F).injective
  have hz : Algebra.trdeg (IntermediateField.adjoin K (Set.range Y))
      (coefficientField (K := K) Y) = 0 := trdeg_eq_zero
  have ht := trdeg_add_eq (A := F) (IntermediateField.adjoin K (Set.range Y))
    (coefficientField (K := K) Y)
  rwa [hz, zero_add] at ht

/-- The actual coefficient field leaves exactly one transcendental
parameter when there is a nonzero vertical derivation in relative degree at most one. -/
theorem coefficientField_trdeg_eq_one (Y : Fin n → F) (D : Derivation K F F)
    (hD : D ≠ 0) (hDY : ∀ i, D (Y i) = 0)
    (htr : Algebra.trdeg (IntermediateField.adjoin K (Set.range Y)) F ≤ 1) :
    Algebra.trdeg (coefficientField (K := K) Y) F = 1 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let : IsScalarTower K (coefficientField (K := K) Y) F := coefficientFieldScalarTower Y
  have hle : Algebra.trdeg (coefficientField (K := K) Y) F ≤ 1 := by
    rw [coefficientField_trdeg_eq_output_trdeg]
    exact htr
  have hne : Algebra.trdeg (coefficientField (K := K) Y) F ≠ 0 := by
    intro hz
    have : Algebra.IsAlgebraic (coefficientField (K := K) Y) F := trdeg_eq_zero_iff.mp hz
    have hkill : ∀ a : coefficientField (K := K) Y,
        D (algebraMap (coefficientField (K := K) Y) F a) = 0 := by
      intro a
      exact vertical_derivation_kills_coefficient_field Y D hDY a
    have he := derivation_eq_zero_of_algebraic_base D hkill
      (fun x => Algebra.IsAlgebraic.isAlgebraic x)
    exact hD he
  exact le_antisymm hle (Cardinal.one_le_iff_ne_zero.mpr hne)

/-- The source function field is a one-variable function field over `L`
for three independent outputs and a nonzero tangent vector. -/
theorem rational_coefficientField_trdeg_eq_one
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (hu : u ≠ 0)
    (hker : rationalJacobian Y *ᵥ u = 0) :
    Algebra.trdeg (coefficientField (K := K) Y) (FractionRing (MvPolynomial (Fin 4) K)) = 1 := by
  apply coefficientField_trdeg_eq_one Y (sourceVectorDerivation u)
    (sourceVectorDerivation_ne_zero u hu) (sourceVectorDerivation_vertical Y u hker)
  apply relative_trdeg_le_one_of_independent_outputs Y hY
  convert rationalSource_trdeg_le (K := K) (n := 4) using 1
  norm_num

/-- Every constructed fiber equation witness has a source function field
of relative transcendence degree one over its actual coefficient field. -/
theorem fiber_witness_trdeg_eq_one
    (H : Fin 4 → FractionRing (MvPolynomial (Fin 4) K))
    (hN : IsNilpotent (rationalJacobian H)) (hrank : (rationalJacobian H).rank = 3)
    (W : FiberEquationWitness H) :
    Algebra.trdeg (coefficientField (K := K) (fun i : Fin 3 => H (W.chart i.castSucc)))
      (FractionRing (MvPolynomial (Fin 4) K)) = 1 := by
  obtain ⟨u, hu0, hu⟩ := matrix_nilpotent_exists_nonzero_kernel _ hN (by omega)
  apply rational_coefficientField_trdeg_eq_one _ W.independent u hu0
  funext i
  exact congrFun hu (W.chart i.castSucc)

end DimensionFourDependence
