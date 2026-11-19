import DimensionFourDependence.Tame

/-! # Stable tameness of the general shear, Proposition 6.4

All maps here are actual automorphisms of `K[x,y,z,t,w]`. In particular,
tameness is asserted in five variables over `K`, with no change of coefficient
ring implicit in the assertion. The point-map word (6.11) is reversed when
viewed as a composition of substitutions on the polynomial algebra.
-/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

variable {K : Type*} [Field K]

/-- A binary coefficient form evaluated in the fixed coordinates `z,t`. -/
noncomputable def base5 (a : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 5) K :=
  aeval ![X 2, X 3] a

theorem base5_notMem (a : MvPolynomial (Fin 2) K) (i : Fin 5)
    (hi2 : i ≠ 2) (hi3 : i ≠ 3) : i ∉ (base5 a).vars := by
  apply Tame.notMem_vars_aeval
  intro j
  fin_cases j <;> simp [vars_X, hi2, hi3]

/-- The invariant `ax+by` in the actual five-variable polynomial ring. -/
noncomputable def invariant5 (a b : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 5) K :=
  base5 a * X 0 + base5 b * X 1

/-- `f(S,z,t)`, with arbitrary polynomial dependence on all three arguments. -/
noncomputable def parameter5 (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 5) K :=
  aeval ![invariant5 a b, X 2, X 3] f

theorem invariant5_notMem_aux (a b : MvPolynomial (Fin 2) K) :
    (4 : Fin 5) ∉ (invariant5 a b).vars := by
  intro h
  rcases Finset.mem_union.mp (vars_add_subset _ _ h) with h | h
  · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
    · exact base5_notMem a 4 (by decide) (by decide) h
    · simpa [vars_X] using h
  · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
    · exact base5_notMem b 4 (by decide) (by decide) h
    · simpa [vars_X] using h

theorem parameter5_notMem_aux (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) : (4 : Fin 5) ∉ (parameter5 a b f).vars := by
  apply Tame.notMem_vars_aeval
  intro j
  fin_cases j
  · exact invariant5_notMem_aux a b
  · simp [vars_X]
  · simp [vars_X]

theorem base5_mul_aux_notMem (a : MvPolynomial (Fin 2) K) (i : Fin 5)
    (hi2 : i ≠ 2) (hi3 : i ≠ 3) (hi4 : i ≠ 4) :
    i ∉ (base5 a * (X 4 : MvPolynomial (Fin 5) K)).vars := by
  intro h
  rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
  · exact base5_notMem a i hi2 hi3 h
  · simpa [vars_X, hi4] using h

/-- The first elementary factor of `A₀`. -/
noncomputable def factorX5 (b : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 5) K ≃ₐ[K] MvPolynomial (Fin 5) K :=
  Tame.elementary 0 (base5 b * X 4)
    (base5_mul_aux_notMem b 0 (by decide) (by decide) (by decide))

/-- The second elementary factor of `A₀`. -/
noncomputable def factorY5 (a : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 5) K ≃ₐ[K] MvPolynomial (Fin 5) K :=
  Tame.elementary 1 (-(base5 a * X 4))
    (by simpa only [vars_neg] using base5_mul_aux_notMem a 1 (by decide) (by decide) (by decide))

/-- The substitution associated to `A₀` in (6.11). -/
noncomputable def factorA5 (a b : MvPolynomial (Fin 2) K) :
    MvPolynomial (Fin 5) K ≃ₐ[K] MvPolynomial (Fin 5) K :=
  factorX5 b * factorY5 a

/-- The substitution associated to the elementary `B₀` in (6.11). -/
noncomputable def factorB5 (a b : MvPolynomial (Fin 2) K) (f : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 5) K ≃ₐ[K] MvPolynomial (Fin 5) K :=
  Tame.elementary 4 (parameter5 a b f) (parameter5_notMem_aux a b f)

theorem factorX5_base (b c : MvPolynomial (Fin 2) K) : factorX5 b (base5 c) = base5 c :=
  Tame.elementary_fixed _ _ _ _ (base5_notMem c 0 (by decide) (by decide))

theorem factorY5_base (a c : MvPolynomial (Fin 2) K) : factorY5 a (base5 c) = base5 c :=
  Tame.elementary_fixed _ _ _ _ (base5_notMem c 1 (by decide) (by decide))

theorem factorA5_base (a b c : MvPolynomial (Fin 2) K) :
    factorA5 a b (base5 c) = base5 c := by
  simp only [factorA5, AlgEquiv.mul_apply, factorX5_base, factorY5_base]

theorem factorA5_X (a b : MvPolynomial (Fin 2) K) (j : Fin 5) :
    factorA5 a b (X j) =
      ![X 0 + base5 b * X 4, X 1 - base5 a * X 4, X 2, X 3, X 4] j := by
  simp only [factorA5, AlgEquiv.mul_apply]
  have hy (k : Fin 5) : factorY5 a (X k) = X k + if k = 1 then -(base5 a * X 4) else 0 :=
    Tame.elementary_X _ _ _ k
  rw [hy j]
  rw [map_add]
  have hx (k : Fin 5) : factorX5 b (X k) = X k + if k = 0 then base5 b * X 4 else 0 :=
    Tame.elementary_X _ _ _ k
  fin_cases j <;> simp [hx, factorX5_base, map_mul, sub_eq_add_neg]

theorem factorA5_invariant (a b : MvPolynomial (Fin 2) K) :
    factorA5 a b (invariant5 a b) = invariant5 a b := by
  simp only [invariant5, map_add, map_mul, factorA5_base, factorA5_X]
  simp
  ring

theorem factorA5_parameter (a b : MvPolynomial (Fin 2) K) (f : MvPolynomial (Fin 3) K) :
    factorA5 a b (parameter5 a b f) = parameter5 a b f := by
  change (factorA5 a b).toAlgHom (aeval ![invariant5 a b, X 2, X 3] f) = _
  rw [Tame.algHom_aeval]
  have hg : (fun j : Fin 3 => factorA5 a b (![invariant5 a b, X 2, X 3] j)) =
      ![invariant5 a b, X 2, X 3] := by
    funext j
    fin_cases j <;> simp [factorA5_invariant, factorA5_X]
  exact congrArg (fun g => aeval g f) hg

theorem factorA5_inv_base (a b c : MvPolynomial (Fin 2) K) :
    (factorA5 a b)⁻¹ (base5 c) = base5 c := by
  apply (factorA5 a b).injective
  simp [factorA5_base]

theorem factorA5_inv_parameter (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    (factorA5 a b)⁻¹ (parameter5 a b f) = parameter5 a b f := by
  apply (factorA5 a b).injective
  simp [factorA5_parameter]

theorem factorA5_inv_X (a b : MvPolynomial (Fin 2) K) (j : Fin 5) :
    (factorA5 a b)⁻¹ (X j) =
      ![X 0 - base5 b * X 4, X 1 + base5 a * X 4, X 2, X 3, X 4] j := by
  apply (factorA5 a b).injective
  fin_cases j <;> simp [factorA5_X, factorA5_base, map_add, map_sub, map_mul]

theorem factorB5_base (a b c : MvPolynomial (Fin 2) K) (f : MvPolynomial (Fin 3) K) :
    factorB5 a b f (base5 c) = base5 c :=
  Tame.elementary_fixed _ _ _ _ (base5_notMem c 4 (by decide) (by decide))

theorem factorB5_inv_base (a b c : MvPolynomial (Fin 2) K) (f : MvPolynomial (Fin 3) K) :
    (factorB5 a b f)⁻¹ (base5 c) = base5 c :=
  Tame.elementary_inv_fixed _ _ _ _ (base5_notMem c 4 (by decide) (by decide))

theorem factorB5_inv_parameter (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    (factorB5 a b f)⁻¹ (parameter5 a b f) = parameter5 a b f :=
  Tame.elementary_inv_fixed _ _ _ _ (parameter5_notMem_aux a b f)

end DimensionFourDependence.Shear
