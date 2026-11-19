import DimensionFourDependence.PlanarInvariantCoefficientDescent

/-! # Recovering the actual invariant-parameter polynomial of the original shear -/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 1500000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "L" => FractionRing R₂
local notation "Aₗ" => MvPolynomial (Fin 2) L
local notation "ι" => (algebraMap R₂ L)

theorem activeFractionPolynomialHom_X_active (j : Fin 2) :
    activeFractionPolynomialHom (X (j.castAdd 2) : R₄) = (X j : Aₗ) := by
  simp only [activeFractionPolynomialHom_apply, activeFractionPolynomial,
    planarCoefficientEquiv_X_active, MvPolynomial.map_X]

theorem activeFractionPolynomialHom_invariant4 (a b : R₂) :
    activeFractionPolynomialHom (invariant4 a b) = (C (ι a) * X 0 + C (ι b) * X 1 : Aₗ) := by
  have hx : activeFractionPolynomialHom (X 0 : R₄) = (X 0 : Aₗ) := activeFractionPolynomialHom_X_active 0
  have hy : activeFractionPolynomialHom (X 1 : R₄) = (X 1 : Aₗ) := activeFractionPolynomialHom_X_active 1
  simp only [invariant4, map_add, map_mul, activeFractionPolynomialHom_base4, hx, hy]

/-- Treat the coefficient variables as the last two parameter
variables in the actual three-variable polynomial used by the shear. -/
noncomputable def planarInvariantParameter3 (f : Polynomial R₂) : R₃ :=
  f.eval₂ (rename (Fin.succ : Fin 2 → Fin 3)).toRingHom (X 0)

theorem parameter4_planarInvariantParameter3 (a b : R₂) (f : Polynomial R₂) :
    parameter4 a b (planarInvariantParameter3 f) =
      f.eval₂ (aeval (![X 2,X 3] : Fin 2 → R₄)).toRingHom (invariant4 a b) := by
  let E : R₃ →ₐ[K] R₄ := aeval ![invariant4 a b, X 2, X 3]
  change E.toRingHom (f.eval₂ (rename (Fin.succ : Fin 2 → Fin 3)).toRingHom (X 0)) = _
  rw [Polynomial.hom_eval₂]
  have hz : E (X 0) = invariant4 a b := aeval_X _ _
  have he : E.comp (rename (Fin.succ : Fin 2 → Fin 3)) = aeval ![X 2, X 3] := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, rename_X]
    fin_cases i <;> simp [E]
  rw [show E.toRingHom (X 0) = invariant4 a b from hz]
  change f.eval₂ (E.comp (rename (Fin.succ : Fin 2 → Fin 3))).toRingHom (invariant4 a b) = _
  rw [he]

/-- The coefficient polynomial over the original base ring evaluates
to the entire original multiplier. Injectivity of coefficient extension
recovers the exact polynomial identity in four variables. -/
theorem parameter4_eq_of_fraction_field_representation
    (a b : R₂) (q : R₄) (f : Polynomial R₂)
    (hq : activeFractionPolynomial q =
      Polynomial.aeval (C (ι a) * X 0 + C (ι b) * X 1 : Aₗ) (f.map ι)) :
    q = parameter4 a b (planarInvariantParameter3 f) := by
  apply activeFractionPolynomial_injective
  change activeFractionPolynomialHom q = activeFractionPolynomialHom _
  rw [parameter4_planarInvariantParameter3, Polynomial.hom_eval₂, activeFractionPolynomialHom_invariant4]
  have he : (activeFractionPolynomialHom (K := K)).comp
      (aeval (![X 2,X 3] : Fin 2 → R₄)).toRingHom = (MvPolynomial.C : L →+* Aₗ).comp ι := by
    apply RingHom.ext
    intro p
    exact activeFractionPolynomialHom_base4 p
  rw [he, ← Polynomial.eval₂_map]
  exact hq

end DimensionFourDependence.Shear
