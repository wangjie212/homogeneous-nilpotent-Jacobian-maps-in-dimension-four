import DimensionFourDependence.TameShear
import DimensionFourDependence.ShearAutomorphism

/-! # Proposition 6.4: inverse, cube-zero Jacobian, and one-stable tameness

The final assertion for coprime homogeneous coefficients of degree at most
one is not part of this module: that assertion uses the separate Lemma 6.2.
-/

namespace DimensionFourDependence.Shear

open MvPolynomial

variable {K : Type*} [Field K]

/-- Adjoining the fifth variable identifies the coefficient polynomials. -/
theorem rename_base4 (a : MvPolynomial (Fin 2) K) :
    rename Fin.castSucc (base4 a) = base5 a := by
  rw [base4, Tame.algHom_aeval]
  have hg : (fun j : Fin 2 => rename Fin.castSucc (![X 2, X 3] j : MvPolynomial (Fin 4) K)) =
      (![X 2, X 3] : Fin 2 → MvPolynomial (Fin 5) K) := by
    funext j
    fin_cases j <;> simp
  exact congrArg (fun g => aeval g a) hg

theorem rename_invariant4 (a b : MvPolynomial (Fin 2) K) :
    rename Fin.castSucc (invariant4 a b) = invariant5 a b := by
  simp [invariant4, invariant5, rename_base4]

theorem rename_parameter4 (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    rename Fin.castSucc (parameter4 a b f) = parameter5 a b f := by
  rw [parameter4, Tame.algHom_aeval]
  have hg : (fun j : Fin 3 => rename Fin.castSucc (![invariant4 a b, X 2, X 3] j)) =
      ![invariant5 a b, X 2, X 3] := by
    funext j
    fin_cases j <;> simp [rename_invariant4]
  exact congrArg (fun g => aeval g f) hg

/-- One-stable tameness means that the actual extension fixing the auxiliary
coordinate lies in the five-variable tame subgroup. -/
def IsOneStablyTame
    (e : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K) : Prop :=
  ∃ E : MvPolynomial (Fin 5) K ≃ₐ[K] MvPolynomial (Fin 5) K,
    E ∈ Tame.subgroup K 5 ∧ E (X 4) = X 4 ∧
      E.toAlgHom.comp (rename Fin.castSucc) = (rename Fin.castSucc).comp e.toAlgHom

/-- The constructed tame automorphism really is the extension of `Ψ` by
one fixed coordinate, as an identity on the entire polynomial algebra. -/
theorem stableAutomorphism5_extends (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    (stableAutomorphism5 a b f).toAlgHom.comp (rename Fin.castSucc) =
      (rename Fin.castSucc).comp (automorphism4 a b f).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro j
  change stableAutomorphism5 a b f (rename Fin.castSucc (X j)) =
    rename Fin.castSucc (automorphism4 a b f (X j))
  rw [rename_X, stableAutomorphism5_X, automorphism4_X]
  fin_cases j <;> simp [perturbation4, rename_base4, rename_parameter4, sub_eq_add_neg]

/-- The one-stable-tameness assertion of Proposition 6.4. -/
theorem automorphism4_oneStablyTame (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) : IsOneStablyTame (automorphism4 a b f) := by
  exact ⟨stableAutomorphism5 a b f, stableAutomorphism5_tame a b f,
    by simpa using stableAutomorphism5_X a b f 4, stableAutomorphism5_extends a b f⟩

/-- Proposition 6.4 through its general, one-stable assertion. No
homogeneity, characteristic-zero or coprimality hypothesis is needed here. -/
theorem proposition_6_4_general (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    (∀ j, automorphism4 a b f (X j) = X j + perturbation4 a b f j) ∧
    (automorphism4 a b f).symm = automorphism4 a b (-f) ∧
    jac (perturbation4 a b f) ^ 3 = 0 ∧ IsOneStablyTame (automorphism4 a b f) :=
  ⟨automorphism4_X a b f, automorphism4_inverse a b f,
    jac_perturbation4_cube a b f, automorphism4_oneStablyTame a b f⟩

end DimensionFourDependence.Shear
