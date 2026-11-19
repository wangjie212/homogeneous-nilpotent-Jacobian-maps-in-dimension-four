import DimensionFourDependence.Tame

/-! # The polynomial quadratic flow used in Lemma 6.2 -/

namespace DimensionFourDependence.QuadraticFlow

open MvPolynomial

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

/-- The quadratic invariant in the actual coordinates `(r,v,u,α)`. -/
noncomputable def quadratic4 : MvPolynomial (Fin 4) K := X 3 * X 0 - X 1 ^ 2

/-- Evaluate a parameter polynomial in `(q,u,α)`. -/
noncomputable def parameter4 (h : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 4) K :=
  aeval ![quadratic4, X 2, X 3] h

theorem parameter4_add (h k : MvPolynomial (Fin 3) K) :
    parameter4 (h + k) = parameter4 h + parameter4 k := map_add _ h k

theorem parameter4_neg (h : MvPolynomial (Fin 3) K) :
    parameter4 (-h) = -parameter4 h := map_neg _ h

/-- The pullback of `T_h=(r+2vh+αh²,v+αh,u,α)`. -/
noncomputable def substitution4 (h : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) K :=
  aeval ![X 0 + 2 * X 1 * parameter4 h + X 3 * parameter4 h ^ 2,
    X 1 + X 3 * parameter4 h, X 2, X 3]

theorem substitution4_X (h : MvPolynomial (Fin 3) K) (j : Fin 4) :
    substitution4 h (X j) =
      ![X 0 + 2 * X 1 * parameter4 h + X 3 * parameter4 h ^ 2,
        X 1 + X 3 * parameter4 h, X 2, X 3] j := by
  simp [substitution4]

/-- Direct polynomial calculation verifies the invariant; no
exponential or locally nilpotent derivation is assumed. -/
theorem substitution4_quadratic (h : MvPolynomial (Fin 3) K) :
    substitution4 h quadratic4 = quadratic4 := by
  simp [quadratic4, map_sub, map_mul, map_pow, substitution4_X]
  ring

/-- Every polynomial parameter in the displayed invariant coordinates
is fixed by every flow in the family. -/
theorem substitution4_parameter (h k : MvPolynomial (Fin 3) K) :
    substitution4 h (parameter4 k) = parameter4 k := by
  rw [parameter4, Tame.algHom_aeval]
  have he : (fun i : Fin 3 => substitution4 h (![quadratic4, X 2, X 3] i)) =
      ![quadratic4, X 2, X 3] := by
    funext i
    fin_cases i <;> simp [substitution4_quadratic, substitution4_X]
  rw [he]

/-- The parameter addition law on the entire original polynomial algebra. -/
theorem substitution4_add (h k : MvPolynomial (Fin 3) K) :
    (substitution4 h).comp (substitution4 k) = substitution4 (h + k) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, substitution4_X]
  have htwo : substitution4 h (2 : MvPolynomial (Fin 4) K) = 2 := by
    exact map_ofNat (substitution4 h) 2
  fin_cases j <;>
    simp [map_add, map_mul, map_pow, substitution4_X, substitution4_parameter,
      parameter4_add, htwo] <;> ring

theorem substitution4_zero :
    substitution4 (0 : MvPolynomial (Fin 3) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [substitution4_X]
  fin_cases j <;> simp [parameter4]

/-- The actual polynomial automorphism; its inverse has parameter `-h`. -/
noncomputable def automorphism4 (h : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  AlgEquiv.ofAlgHom (substitution4 h) (substitution4 (-h))
    (by rw [substitution4_add, add_neg_cancel, substitution4_zero])
    (by rw [substitution4_add, neg_add_cancel, substitution4_zero])

theorem automorphism4_X (h : MvPolynomial (Fin 3) K) (j : Fin 4) :
    automorphism4 h (X j) =
      ![X 0 + 2 * X 1 * parameter4 h + X 3 * parameter4 h ^ 2,
        X 1 + X 3 * parameter4 h, X 2, X 3] j := substitution4_X h j

theorem automorphism4_quadratic (h : MvPolynomial (Fin 3) K) :
    automorphism4 h quadratic4 = quadratic4 := substitution4_quadratic h

theorem automorphism4_parameter (h k : MvPolynomial (Fin 3) K) :
    automorphism4 h (parameter4 k) = parameter4 k := substitution4_parameter h k

theorem automorphism4_add (h k : MvPolynomial (Fin 3) K) :
    automorphism4 (h + k) = automorphism4 h * automorphism4 k := by
  apply AlgEquiv.ext
  intro P
  exact (AlgHom.congr_fun (substitution4_add h k) P).symm

theorem automorphism4_zero : automorphism4 (0 : MvPolynomial (Fin 3) K) = 1 := by
  apply AlgEquiv.ext
  intro P
  exact AlgHom.congr_fun substitution4_zero P

end DimensionFourDependence.QuadraticFlow
