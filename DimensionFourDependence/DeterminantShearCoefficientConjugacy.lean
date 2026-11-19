import DimensionFourDependence.DeterminantShearFamily
import DimensionFourDependence.DeterminantShearCoefficientIdentity

/-! # Actual coefficient shears preserve the determinant and shear family -/

namespace DimensionFourDependence.DeterminantShear

open MvPolynomial

set_option maxHeartbeats 2500000

variable {K : Type*} [Field K]

theorem coefficient_linear_parameter_notMem (r : K) (i j : Fin 4) (hne : i ≠ j) :
    i ∉ (C r * X j : MvPolynomial (Fin 4) K).vars := by
  intro h
  rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
  · simpa only [vars_C, Finset.notMem_empty] using h
  · exact hne (by simpa only [vars_X, Finset.mem_singleton] using h)

noncomputable def rowCoefficientShift4 (r : K) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  Tame.elementary 1 (C r * X 0) (coefficient_linear_parameter_notMem r 1 0 (by decide))

noncomputable def baseCoefficientShift4 (r : K) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  Tame.elementary 2 (C r * X 3) (coefficient_linear_parameter_notMem r 2 3 (by decide))

/-- Right multiplication of the two-by-two determinant coordinates
by a unipotent constant matrix, as two actual elementary maps. -/
noncomputable def coefficientShift4 (r : K) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  rowCoefficientShift4 r * baseCoefficientShift4 r

theorem coefficientShift4_X (r : K) (j : Fin 4) :
    coefficientShift4 r (X j) = ![X 0, X 1 + C r * X 0, X 2 + C r * X 3, X 3] j := by
  have hC (c : K) : rowCoefficientShift4 r (C c) =
      (C c : MvPolynomial (Fin 4) K) := (rowCoefficientShift4 r).commutes c
  have hrow (i : Fin 4) : rowCoefficientShift4 r (X i) =
      X i + if i = 1 then C r * X 0 else 0 := Tame.elementary_X _ _ _ i
  have hbase (i : Fin 4) : baseCoefficientShift4 r (X i) =
      X i + if i = 2 then C r * X 3 else 0 := Tame.elementary_X _ _ _ i
  fin_cases j <;>
    simp [coefficientShift4, AlgEquiv.mul_apply, hrow, hbase, map_add, map_mul, hC]

theorem coefficientShift4_inv_X (r : K) (j : Fin 4) :
    (coefficientShift4 r)⁻¹ (X j) = ![X 0, X 1 - C r * X 0, X 2 - C r * X 3, X 3] j := by
  apply (coefficientShift4 r).injective
  have hC (c : K) : coefficientShift4 r (C c) = C c := (coefficientShift4 r).commutes c
  fin_cases j <;> simp [coefficientShift4_X, map_sub, map_mul, hC]

theorem coefficientShift4_invariant (r : K) :
    coefficientShift4 r invariant4 = invariant4 := by
  simp [invariant4, coefficientShift4_X]
  ring

noncomputable def coefficientParameterShift3 (r : K) :
    MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval ![X 0, X 1 + C r * X 2, X 2]

theorem coefficientShift4_parameter (r : K) (f : MvPolynomial (Fin 3) K) :
    coefficientShift4 r (parameter4 f) = parameter4 (coefficientParameterShift3 r f) := by
  change (coefficientShift4 r).toAlgHom (aeval ![invariant4, X 2, X 3] f) = _
  rw [Tame.algHom_aeval]
  unfold parameter4 coefficientParameterShift3
  rw [comp_aeval_apply]
  have he : (fun i : Fin 3 => coefficientShift4 r (![invariant4, X 2, X 3] i)) =
      (fun i : Fin 3 => (aeval (![invariant4, X 2, X 3] : Fin 3 → MvPolynomial (Fin 4) K))
        ((![X 0, X 1 + C r * X 2, X 2] : Fin 3 → MvPolynomial (Fin 3) K) i)) := by
    funext i
    fin_cases i <;> simp [coefficientShift4_invariant, coefficientShift4_X]
  simpa only [AlgEquiv.coe_toAlgHom] using
    congrArg (fun g : Fin 3 → MvPolynomial (Fin 4) K => aeval g f) he

/-- The determinant-preserving coefficient shear transports the
entire family with its row-operation coefficients unchanged. -/
theorem automorphism4_coefficient_shift_conjugacy
    (r : K) (f : MvPolynomial (Fin 3) K) :
    automorphism4 (coefficientParameterShift3 r f) =
      coefficientShift4 r * automorphism4 f * (coefficientShift4 r)⁻¹ := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro j
  change automorphism4 (coefficientParameterShift3 r f) (X j) =
    (coefficientShift4 r * automorphism4 f * (coefficientShift4 r)⁻¹) (X j)
  have hc := coefficient_conjugacy_coordinate_identity
    (coefficientShift4 r).toAlgHom (automorphism4 f).toAlgHom
    ((coefficientShift4 r)⁻¹).toAlgHom
    (X : Fin 4 → MvPolynomial (Fin 4) K) (C r)
    (parameter4 f) (parameter4 (coefficientParameterShift3 r f))
    (coefficientShift4_X r) (coefficientShift4_inv_X r) (automorphism4_X f)
    ((automorphism4 f).commutes r) ((coefficientShift4 r).commutes r)
    (coefficientShift4_parameter r f) j
  rw [automorphism4_X]
  exact hc.symm

theorem automorphism4_coefficient_shift_tame (r : K) (f : MvPolynomial (Fin 3) K)
    (hf : automorphism4 f ∈ Tame.subgroup K 4) :
    automorphism4 (coefficientParameterShift3 r f) ∈ Tame.subgroup K 4 := by
  rw [automorphism4_coefficient_shift_conjugacy]
  have he : coefficientShift4 r ∈ Tame.subgroup K 4 :=
    (Tame.subgroup K 4).mul_mem (Tame.elementary_mem _ _ _) (Tame.elementary_mem _ _ _)
  exact (Tame.subgroup K 4).mul_mem ((Tame.subgroup K 4).mul_mem he hf)
    ((Tame.subgroup K 4).inv_mem he)

end DimensionFourDependence.DeterminantShear
