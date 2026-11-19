import DimensionFourDependence.ShearJacobian

/-! # The four-variable inverse in Proposition 6.4 -/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

@[irreducible] noncomputable def substitution4 (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) K :=
  aeval ![X 0 + base4 b * parameter4 a b f, X 1 - base4 a * parameter4 a b f, X 2, X 3]

theorem substitution4_X (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) (j : Fin 4) :
    substitution4 a b f (X j) =
      ![X 0 + base4 b * parameter4 a b f, X 1 - base4 a * parameter4 a b f, X 2, X 3] j := by
  simp [substitution4]

theorem substitution4_base (a b c : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) : substitution4 a b f (base4 c) = base4 c := by
  rw [base4, Tame.algHom_aeval]
  have hg : (fun j : Fin 2 => substitution4 a b f (![X 2, X 3] j)) = ![X 2, X 3] := by
    funext j
    fin_cases j <;> simp [substitution4_X]
  exact congrArg (fun g => aeval g c) hg

theorem substitution4_invariant (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    substitution4 a b f (invariant4 a b) = invariant4 a b := by
  simp only [invariant4, map_add, map_mul, substitution4_base, substitution4_X]
  simp
  ring

theorem substitution4_parameter (a b : MvPolynomial (Fin 2) K)
    (f g : MvPolynomial (Fin 3) K) :
    substitution4 a b f (parameter4 a b g) = parameter4 a b g := by
  rw [parameter4, Tame.algHom_aeval]
  have hg : (fun j : Fin 3 => substitution4 a b f (![invariant4 a b, X 2, X 3] j)) =
      ![invariant4 a b, X 2, X 3] := by
    funext j
    fin_cases j <;> simp [substitution4_invariant, substitution4_X]
  exact congrArg (fun g' => aeval g' g) hg

theorem parameter4_add (a b : MvPolynomial (Fin 2) K)
    (f g : MvPolynomial (Fin 3) K) :
    parameter4 a b (f + g) = parameter4 a b f + parameter4 a b g :=
  map_add (aeval ![invariant4 a b, X 2, X 3]) f g

end DimensionFourDependence.Shear
