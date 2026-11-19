import DimensionFourDependence.Proposition64
import DimensionFourDependence.DeterminantShearCoefficientConjugacy

/-! # Ordinary tameness of shears with a zero or constant coefficient pair -/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K

theorem base4_notMem_active (a : MvPolynomial (Fin 2) K) (i : Fin 4)
    (hi2 : i ≠ 2) (hi3 : i ≠ 3) : i ∉ (base4 a).vars := by
  apply Tame.notMem_vars_aeval
  intro j
  fin_cases j <;> simp [hi2, hi3]

theorem base4_C (c : K) : base4 (C c : MvPolynomial (Fin 2) K) = C c := by
  simp [base4]

/-- A zero first coefficient makes the original automorphism elementary. -/
theorem automorphism4_zero_left_tame (b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) : automorphism4 0 b f ∈ Tame.subgroup K 4 := by
  have hb : (0 : Fin 4) ∉ (base4 b).vars := base4_notMem_active b 0 (by decide) (by decide)
  have hz : base4 (0 : MvPolynomial (Fin 2) K) = 0 := map_zero (aeval ![X 2, X 3])
  have hp : (0 : Fin 4) ∉ (parameter4 0 b f).vars := by
    unfold parameter4
    apply Tame.notMem_vars_aeval
    intro j
    fin_cases j
    · simp only [Matrix.cons_val_zero, invariant4, hz, zero_mul, zero_add]
      intro h
      exact (Finset.mem_union.mp (vars_mul _ _ h)).elim hb (by simp)
    · simp
    · simp
  apply Subgroup.subset_closure
  right
  refine ⟨0, base4 b * parameter4 0 b f, ?_, ?_⟩
  · intro h
    exact (Finset.mem_union.mp (vars_mul _ _ h)).elim hb hp
  · intro j
    rw [automorphism4_X]
    fin_cases j <;> simp [perturbation4, hz]

/-- With constant coefficients, a linear shear in the two active
coordinates turns the invariant into a scalar multiple of one coordinate. -/
theorem automorphism4_constant_coefficients_tame (a b : K)
    (f : MvPolynomial (Fin 3) K) : automorphism4 (C a) (C b) f ∈ Tame.subgroup K 4 := by
  classical
  by_cases ha : a = 0
  · simpa [ha] using automorphism4_zero_left_tame (C b) f
  let c : K := b / a
  let p : R₄ := aeval ![C a * X 0, X 2, X 3] f
  have hp : (1 : Fin 4) ∉ (-(C a * p)).vars := by
    have hv : (1 : Fin 4) ∉ p.vars := by
      apply Tame.notMem_vars_aeval
      intro j
      fin_cases j
      · exact DeterminantShear.coefficient_linear_parameter_notMem a 1 0 (by decide)
      · simp
      · simp
    rw [vars_neg]
    intro h
    exact (Finset.mem_union.mp (vars_mul _ _ h)).elim (by simp) hv
  let E := Tame.elementary (0 : Fin 4) (C c * X 1)
    (DeterminantShear.coefficient_linear_parameter_notMem c 0 1 (by decide))
  let F := Tame.elementary (1 : Fin 4) (-(C a * p)) hp
  have hE (j : Fin 4) : E (X j) = X j + if j = 0 then C c * X 1 else 0 :=
    Tame.elementary_X _ _ _ j
  have hI (j : Fin 4) : E⁻¹ (X j) = X j + if j = 0 then -(C c * X 1) else 0 :=
    Tame.elementary_inv_X _ _ _ j
  have hF (j : Fin 4) : F (X j) = X j + if j = 1 then -(C a * p) else 0 :=
    Tame.elementary_X _ _ _ j
  have hEC (d : K) : E (C d) = C d := E.commutes d
  have hFC (d : K) : F (C d) = C d := F.commutes d
  have hac : C a * C c = (C b : R₄) := by
    rw [← map_mul]
    congr 1
    dsimp [c]
    exact mul_div_cancel₀ b ha
  have hEp : E p = parameter4 (C a) (C b) f := by
    change E.toAlgHom (aeval ![C a * X 0, X 2, X 3] f) = _
    rw [Tame.algHom_aeval]
    have h : (fun j : Fin 3 => E ((![C a * X 0, X 2, X 3] : Fin 3 → R₄) j)) =
        ![invariant4 (C a) (C b), X 2, X 3] := by
      funext j
      fin_cases j <;> simp [hE, hEC, invariant4, base4_C, mul_add, ← mul_assoc, hac]
    simpa only [parameter4, AlgEquiv.coe_toAlgHom] using
      congrArg (fun v : Fin 3 → R₄ => aeval v f) h
  have he : automorphism4 (C a) (C b) f = E * F * E⁻¹ := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply MvPolynomial.algHom_ext
    intro j
    change automorphism4 (C a) (C b) f (X j) = E (F (E⁻¹ (X j)))
    rw [automorphism4_X, hI]
    fin_cases j <;>
      simp [perturbation4, base4_C, map_add, map_mul, map_neg, hE, hF, hEC, hFC, hEp]
    linear_combination -(parameter4 (C a) (C b) f) * hac
  rw [he]
  have htE : E ∈ Tame.subgroup K 4 := Tame.elementary_mem _ _ _
  have htF : F ∈ Tame.subgroup K 4 := Tame.elementary_mem _ _ _
  exact (Tame.subgroup K 4).mul_mem ((Tame.subgroup K 4).mul_mem htE htF)
    ((Tame.subgroup K 4).inv_mem htE)

end DimensionFourDependence.Shear
