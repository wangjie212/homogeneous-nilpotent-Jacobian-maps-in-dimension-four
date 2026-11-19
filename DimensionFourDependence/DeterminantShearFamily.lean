import DimensionFourDependence.Tame

/-! # The actual determinant-preserving shear family in Lemma 6.2 -/

namespace DimensionFourDependence.DeterminantShear

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

noncomputable def invariant4 : MvPolynomial (Fin 4) K := X 2 * X 0 - X 3 * X 1

noncomputable def parameter4 (f : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 4) K :=
  aeval ![invariant4, X 2, X 3] f

noncomputable def substitution4 (f : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) K :=
  aeval ![X 0 + X 3 * parameter4 f, X 1 + X 2 * parameter4 f, X 2, X 3]

theorem substitution4_X (f : MvPolynomial (Fin 3) K) (j : Fin 4) :
    substitution4 f (X j) =
      ![X 0 + X 3 * parameter4 f, X 1 + X 2 * parameter4 f, X 2, X 3] j := by
  simp [substitution4]

theorem substitution4_invariant (f : MvPolynomial (Fin 3) K) :
    substitution4 f invariant4 = invariant4 := by
  simp [invariant4, substitution4_X]
  ring

theorem substitution4_parameter (f g : MvPolynomial (Fin 3) K) :
    substitution4 f (parameter4 g) = parameter4 g := by
  rw [parameter4, Tame.algHom_aeval]
  have he : (fun i : Fin 3 => substitution4 f (![invariant4, X 2, X 3] i)) =
      ![invariant4, X 2, X 3] := by
    funext i
    fin_cases i <;> simp [substitution4_invariant, substitution4_X]
  exact congrArg (fun v => aeval v g) he

theorem substitution4_add (f g : MvPolynomial (Fin 3) K) :
    (substitution4 f).comp (substitution4 g) = substitution4 (f + g) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, substitution4_X]
  fin_cases j <;>
    simp [map_add, map_mul, substitution4_X, substitution4_parameter,
      show parameter4 (f + g) = parameter4 f + parameter4 g from map_add _ _ _] <;> ring

theorem substitution4_zero :
    substitution4 (0 : MvPolynomial (Fin 3) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [substitution4_X]
  fin_cases j <;> simp [parameter4]

/-- The actual automorphism with polynomial coordinates (6.2). -/
noncomputable def automorphism4 (f : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  AlgEquiv.ofAlgHom (substitution4 f) (substitution4 (-f))
    (by rw [substitution4_add, add_neg_cancel, substitution4_zero])
    (by rw [substitution4_add, neg_add_cancel, substitution4_zero])

theorem automorphism4_X (f : MvPolynomial (Fin 3) K) (j : Fin 4) :
    automorphism4 f (X j) =
      ![X 0 + X 3 * parameter4 f, X 1 + X 2 * parameter4 f, X 2, X 3] j :=
  substitution4_X f j

theorem automorphism4_invariant (f : MvPolynomial (Fin 3) K) :
    automorphism4 f invariant4 = invariant4 := substitution4_invariant f

theorem automorphism4_parameter (f g : MvPolynomial (Fin 3) K) :
    automorphism4 f (parameter4 g) = parameter4 g := substitution4_parameter f g

theorem automorphism4_add (f g : MvPolynomial (Fin 3) K) :
    automorphism4 (f + g) = automorphism4 f * automorphism4 g := by
  apply AlgEquiv.ext
  intro P
  exact (AlgHom.congr_fun (substitution4_add f g) P).symm

theorem automorphism4_zero : automorphism4 (0 : MvPolynomial (Fin 3) K) = 1 := by
  apply AlgEquiv.ext
  intro P
  exact AlgHom.congr_fun substitution4_zero P

end DimensionFourDependence.DeterminantShear
