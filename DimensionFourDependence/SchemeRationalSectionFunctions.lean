import DimensionFourDependence.Defs
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.LocalPredicate

/-! # Regular scheme sections as functions in the actual rational function field

The pointwise construction also works on the empty open. It gives the
scalar action required for a fractional module sheaf without selecting
a point or assuming the open is nonempty.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

variable (X : Scheme.{u}) [IsIntegral X]

/-- Every regular section gives its rational value at every point,
through the actual stalk and the actual scheme function field. -/
noncomputable def schemeRationalSectionFunction (U : X.Opens) :
    Γ(X, U) →+* (U → X.functionField) where
  toFun r p := algebraMap (X.presheaf.stalk p.1) X.functionField (X.presheaf.germ U p.1 p.2 r)
  map_zero' := by funext p; simp
  map_one' := by funext p; simp
  map_add' := by intro r s; funext p; simp
  map_mul' := by intro r s; funext p; simp

/-- The actual rational-value function respects restriction of regular
sections, point by point on every smaller open. -/
theorem schemeRationalSectionFunction_res
    {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, V)) (p : U) :
    schemeRationalSectionFunction X U (X.presheaf.map i.op r) p =
      schemeRationalSectionFunction X V r (i p) := by
  change algebraMap (X.presheaf.stalk p.1) X.functionField
      (X.presheaf.germ U p.1 p.2 (X.presheaf.map i.op r)) = _
  rw [X.presheaf.germ_res_apply]
  rfl

/-- On a nonempty open the rational function is its actual generic
germ, independently of the point used in its regular representative. -/
theorem schemeRationalSectionFunction_eq_generic
    (U : X.Opens) [Nonempty U] (r : Γ(X, U)) (p : U) :
    schemeRationalSectionFunction X U r p = X.germToFunctionField U r :=
  Scheme.algebraMap_germ_eq_germToFunctionField X p.2 r

/-- The pointwise rational realization is faithful on a nonempty open. -/
theorem schemeRationalSectionFunction_injective
    (U : X.Opens) [hU : Nonempty U] : Function.Injective (schemeRationalSectionFunction X U) := by
  intro r s hrs
  let p : U := Classical.choice hU
  apply X.germToFunctionField_injective U
  have h := congrFun hrs p
  simpa only [schemeRationalSectionFunction_eq_generic] using h

/-- The original structure sheaf acts on rational-valued functions
on every open, including the empty open, by its actual germ values. -/
@[instance_reducible]
noncomputable def schemeRationalFunctionAlgebra (U : X.Opens) :
    Algebra Γ(X, U) (U → X.functionField) := (schemeRationalSectionFunction X U).toAlgebra

end DimensionFourDependence
