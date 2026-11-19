import DimensionFourDependence.RelativeClosureCoordinateTransport
import DimensionFourDependence.FullOutputLinearCoordinates
import DimensionFourDependence.TernaryIndependentOutputChart

/-! # The coefficient field is intrinsic under a ternary chart change -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 1850000

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- An actual source automorphism transports the entire relative
algebraic closure of a specified coefficient subfield. -/
theorem relative_algebraic_closure_map_source_equiv
    (B : IntermediateField K F) (f : F ≃ₐ[K] F) :
    ((algebraicClosure B F).restrictScalars K).map f.toAlgHom =
      (algebraicClosure (B.map f.toAlgHom) F).restrictScalars K := by
  let e := IntermediateField.intermediateFieldMap f B
  have hcompat : (algebraMap (B.map f.toAlgHom) F).comp e.toRingHom =
      f.toRingHom.comp (algebraMap B F) := by
    ext c
    rfl
  have he (a : F) : IsAlgebraic (B.map f.toAlgHom) (f a) ↔ IsAlgebraic B a :=
    isAlgebraic_ringHom_iff_of_comp_eq e.toRingEquiv f.toRingHom f.injective hcompat
  ext a
  change (∃ z ∈ algebraicClosure B F, f z = a) ↔ a ∈ algebraicClosure (B.map f.toAlgHom) F
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mem_algebraicClosure_iff.mpr ((he z).mpr (mem_algebraicClosure_iff.mp hz))
  · intro ha
    refine ⟨f.symm a, mem_algebraicClosure_iff.mpr ((he (f.symm a)).mp ?_), f.apply_symm_apply a⟩
    simpa only [f.apply_symm_apply] using mem_algebraicClosure_iff.mp ha

/-- When the last output is algebraic over the first pair, the
coefficient field consists of exactly the elements algebraic over all
three outputs. -/
theorem ternary_coefficientField_eq_relative_fullOutputClosure
    (H : Fin 3 → F)
    (hw : IsAlgebraic (IntermediateField.adjoin K (Set.range (fun i : Fin 2 => H i.castSucc))) (H 2)) :
    (coefficientField (K := K) (fun i : Fin 2 => H i.castSucc)).restrictScalars K =
      (algebraicClosure (fullOutputField (K := K) H) F).restrictScalars K := by
  let Y := fun i : Fin 2 => H i.castSucc
  let L := coefficientField (K := K) Y
  let B := IntermediateField.adjoin K (Set.range Y)
  let M := fullOutputField (K := K) H
  have hBM : B ≤ M := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin K _ ⟨i.castSucc, rfl⟩
  have hML : M ≤ L.restrictScalars K := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact mem_algebraicClosure_iff.mpr hw
    · have hmem : Y j ∈ B := IntermediateField.subset_adjoin K _ ⟨j, rfl⟩
      exact mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (A := F) (⟨Y j, hmem⟩ : B))
  let : Algebra B M := (IntermediateField.inclusion hBM).toRingHom.toAlgebra
  let : IsScalarTower B M F := IsScalarTower.of_algebraMap_eq (by intro b; rfl)
  let : Algebra.IsAlgebraic B M := ⟨fun m =>
    (isAlgebraic_algebraMap_iff (algebraMap M F).injective).mp
      (mem_algebraicClosure_iff.mp (hML m.property))⟩
  ext a
  change a ∈ algebraicClosure B F ↔ a ∈ algebraicClosure M F
  rw [mem_algebraicClosure_iff, mem_algebraicClosure_iff]
  exact ⟨fun h => h.tower_top M, fun h => h.restrictScalars B⟩

variable [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F₃" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F₃)

/-- Independent charts before and after constant conjugacy use the
same intrinsic coefficient field under the actual source automorphism. -/
theorem ternary_chart_coefficientField_map_linearPolynomialConjugate
    (T S : Matrix (Fin 3) (Fin 3) K) (hTS : T * S = 1) (hST : S * T = 1)
    (H : Fin 3 → R₃) (hN : IsNilpotent (jac H))
    (hY : AlgebraicIndependent K (fun i : Fin 2 => ι (H i.castSucc)))
    (hY' : AlgebraicIndependent K
      (fun i : Fin 2 => ι (linearPolynomialConjugate T S H i.castSucc))) :
    ((coefficientField (K := K) (fun i : Fin 2 => ι (H i.castSucc))).restrictScalars K).map
        (matrixSourceFractionEquiv T S hTS hST).toAlgHom =
      (coefficientField (K := K) (fun i : Fin 2 =>
        ι (linearPolynomialConjugate T S H i.castSucc))).restrictScalars K := by
  let G := linearPolynomialConjugate T S H
  have hGn := linearPolynomialConjugate_nilpotent T S hTS hST H hN
  have hclosure := ternary_coefficientField_eq_relative_fullOutputClosure
    (K := K) (fun i => ι (H i)) (ternary_nilpotent_independent_pair_last_output_is_algebraic H hN hY)
  have hclosure' := ternary_coefficientField_eq_relative_fullOutputClosure
    (K := K) (fun i => ι (G i)) (ternary_nilpotent_independent_pair_last_output_is_algebraic G hGn hY')
  rw [hclosure, hclosure', relative_algebraic_closure_map_source_equiv]
  change (algebraicClosure ((polynomialOutputField H).map (matrixSourceFractionEquiv T S hTS hST).toAlgHom)
      F₃).restrictScalars K = (algebraicClosure (polynomialOutputField G) F₃).restrictScalars K
  rw [polynomialOutputField_linearPolynomialConjugate T S hTS hST H]

end DimensionFourDependence
