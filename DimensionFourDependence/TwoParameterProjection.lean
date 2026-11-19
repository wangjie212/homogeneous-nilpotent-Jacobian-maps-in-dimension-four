import DimensionFourDependence.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # The two actual coordinates in an iterated rational projection field -/

namespace DimensionFourDependence

open MvPolynomial

variable (k : Type*) [Field k]

/-- The outer rational variable and the inner rational parameter in
the actual two-variable projection field, in this coordinate order. -/
noncomputable def twoParameterProjectionCoordinates :
    Option Unit → FractionRing (Polynomial (RatFunc k)) :=
  fun i => i.elim
    (algebraMap (Polynomial (RatFunc k)) (FractionRing (Polynomial (RatFunc k))) Polynomial.X)
    (fun _ => algebraMap (RatFunc k) (FractionRing (Polynomial (RatFunc k))) RatFunc.X)

/-- These specified projection coordinates are algebraically independent
over the original constants; this property is constructed, not assumed. -/
theorem twoParameterProjectionCoordinates_algebraicIndependent :
    AlgebraicIndependent k (twoParameterProjectionCoordinates k) := by
  let C := RatFunc k
  let T := FractionRing (Polynomial C)
  let c : MvPolynomial Unit k →ₐ[k] C := MvPolynomial.aeval (fun _ => RatFunc.X)
  have hc : Function.Injective c := by
    apply algebraicIndependent_iff_injective_aeval.mp
    exact algebraicIndependent_unique_type_iff.mpr RatFunc.transcendental_X
  let φ : MvPolynomial (Option Unit) k →ₐ[k] T :=
    (IsScalarTower.toAlgHom k (Polynomial C) T).comp
      ((Polynomial.mapAlgHom c).comp (optionEquivLeft k Unit).toAlgHom)
  have hφ : MvPolynomial.aeval (twoParameterProjectionCoordinates k) = φ := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none =>
      simp [φ, c, twoParameterProjectionCoordinates]
      rfl
    | some j =>
      simp [φ, c, twoParameterProjectionCoordinates]
      exact IsScalarTower.algebraMap_apply C (Polynomial C) T RatFunc.X
  apply algebraicIndependent_iff_injective_aeval.mpr
  rw [hφ]
  exact (IsFractionRing.injective (Polynomial C) T).comp
    ((Polynomial.map_injective c.toRingHom hc).comp (optionEquivLeft k Unit).injective)

end DimensionFourDependence
