import DimensionFourDependence.Defs
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.RingTheory.Derivation.MapCoeffs

/-! # Regrouping ternary source polynomials by their last variable -/

namespace DimensionFourDependence

open MvPolynomial

universe u
set_option maxHeartbeats 1750000

variable {K : Type u} [Field K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "P" => Polynomial R₂

/-- View the last source variable as the ordinary polynomial variable. -/
noncomputable def ternaryLastVariableEquiv : R₃ ≃ₐ[K] P :=
  (renameEquiv K (finSuccEquiv' (Fin.last 2))).trans (optionEquivLeft K (Fin 2))

theorem ternaryLastVariableEquiv_C (a : K) :
    ternaryLastVariableEquiv (C a) = Polynomial.C (C a) := by
  simp only [ternaryLastVariableEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_C,
    optionEquivLeft_C]

theorem ternaryLastVariableEquiv_X_last :
    ternaryLastVariableEquiv (K := K) (X (Fin.last 2)) = Polynomial.X := by
  simp only [ternaryLastVariableEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
    finSuccEquiv'_at, optionEquivLeft_X_none]

theorem ternaryLastVariableEquiv_X_castSucc (i : Fin 2) :
    ternaryLastVariableEquiv (K := K) (X i.castSucc) = Polynomial.C (X i) := by
  simp only [ternaryLastVariableEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
    finSuccEquiv'_last_apply_castSucc, optionEquivLeft_X_some]

/-- Differentiation in an active source variable acts on the
coefficients of the regrouped polynomial. -/
noncomputable def ternaryCoefficientPartial (i : Fin 2) : Derivation K P P :=
  PolynomialModule.equivPolynomialSelf.compDer (pderiv i).mapCoeffs

theorem ternaryCoefficientPartial_coeff (i : Fin 2) (p : P) (d : ℕ) :
    (ternaryCoefficientPartial i p).coeff d = pderiv i (p.coeff d) := rfl

theorem ternaryCoefficientPartial_C (i : Fin 2) (a : R₂) :
    ternaryCoefficientPartial i (Polynomial.C a) = Polynomial.C (pderiv i a) := by
  apply Polynomial.ext
  intro d
  simp only [ternaryCoefficientPartial_coeff, Polynomial.coeff_C]
  split_ifs <;> simp

theorem ternaryCoefficientPartial_X (i : Fin 2) :
    ternaryCoefficientPartial (K := K) i Polynomial.X = 0 := by
  apply Polynomial.ext
  intro d
  simp only [ternaryCoefficientPartial_coeff, Polynomial.coeff_X, Polynomial.coeff_zero]
  split_ifs <;> simp

private theorem regroup_derivation_of_coordinates (g : R₃ →ₐ[K] P)
    (D : Derivation K P P) (i : Fin 3) (hX : ∀ j, g (pderiv i (X j)) = D (g (X j)))
    (p : R₃) : g (pderiv i p) = D (g p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [pderiv_C, map_zero]
    rw [← algebraMap_eq, g.commutes, D.map_algebraMap]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a j ha =>
    rw [pderiv_mul, map_add, map_mul, map_mul, ha, hX, map_mul, D.leibniz, smul_eq_mul, smul_eq_mul]
    ac_rfl

/-- An active formal partial is precisely the coefficient derivation
in the regrouped polynomial ring. -/
theorem ternaryLastVariableEquiv_active_pderiv (i : Fin 2) (p : R₃) :
    ternaryLastVariableEquiv (pderiv i.castSucc p) =
      ternaryCoefficientPartial i (ternaryLastVariableEquiv p) := by
  apply regroup_derivation_of_coordinates ternaryLastVariableEquiv.toAlgHom
  intro j
  change ternaryLastVariableEquiv (pderiv i.castSucc (X j)) =
    ternaryCoefficientPartial i (ternaryLastVariableEquiv (X j))
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [pderiv_X_of_ne (Fin.castSucc_ne_last i).symm, map_zero,
      ternaryLastVariableEquiv_X_last, ternaryCoefficientPartial_X]
  · rw [ternaryLastVariableEquiv_X_castSucc, ternaryCoefficientPartial_C, pderiv_X, pderiv_X]
    by_cases h : k = i
    · subst k
      simp [Pi.single_apply]
    · simp [h, Ne.symm h, Fin.castSucc_inj, Pi.single_apply]

/-- The last formal partial is the ordinary polynomial derivative in
the regrouped last variable. -/
theorem ternaryLastVariableEquiv_last_pderiv (p : R₃) :
    ternaryLastVariableEquiv (pderiv (Fin.last 2) p) = (ternaryLastVariableEquiv p).derivative := by
  let D : Derivation K P P := (Polynomial.mkDerivation R₂ (1 : P)).restrictScalars K
  have hD (q : P) : D q = q.derivative := by
    change Polynomial.mkDerivation R₂ (1 : P) q = q.derivative
    rw [Polynomial.mkDerivation_apply, Algebra.smul_def, mul_one]
    rfl
  rw [← hD]
  apply regroup_derivation_of_coordinates ternaryLastVariableEquiv.toAlgHom
  intro j
  change ternaryLastVariableEquiv (pderiv (Fin.last 2) (X j)) = D (ternaryLastVariableEquiv (X j))
  rw [hD]
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [pderiv_X_self, map_one, ternaryLastVariableEquiv_X_last, Polynomial.derivative_X]
  · rw [pderiv_X_of_ne (Fin.castSucc_ne_last k), map_zero,
      ternaryLastVariableEquiv_X_castSucc, Polynomial.derivative_C]

end DimensionFourDependence
