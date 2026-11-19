import DimensionFourDependence.ReducedPointClosureScheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Reduced morphisms into a point closure factor through its closed scheme -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A morphism from a reduced scheme has the vanishing ideal of its
topological image closure as its scheme-theoretic kernel. -/
theorem reduced_scheme_morphism_ker
    {X Y : Scheme.{u}} [IsReduced Y] (f : Y ⟶ X) :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range f)) := by
  have htop : (⊥ : Y.IdealSheafData) = Scheme.IdealSheafData.vanishingIdeal ⊤ := by
    simp [Scheme.nilradical_eq_bot]
  rw [← Scheme.IdealSheafData.map_bot, htop, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  simp only [Closeds.coe_top, Set.image_univ]

/-- Containment of the actual topological image in a point closure
gives the ideal containment needed by its closed-immersion universal property. -/
theorem reduced_point_closure_ideal_le_ker
    {X Y : Scheme.{u}} [IsReduced Y] (x : X) (f : Y ⟶ X)
    (h : Set.range f ⊆ closure {x}) : reducedPointClosureIdeal X x ≤ f.ker := by
  rw [reduced_scheme_morphism_ker]
  apply Scheme.IdealSheafData.vanishingIdeal_antimono
  exact closure_minimal h isClosed_closure

/-- The actual factorization through the integral reduced point closure. -/
noncomputable def reducedPointClosureLift
    {X Y : Scheme.{u}} [IsReduced Y] (x : X) (f : Y ⟶ X)
    (h : Set.range f ⊆ closure {x}) : Y ⟶ reducedPointClosureScheme X x := by
  let : IsClosedImmersion (reducedPointClosureInclusion X x) :=
    reducedPointClosureInclusion_isClosedImmersion X x
  apply IsClosedImmersion.lift (reducedPointClosureInclusion X x) f
  change (reducedPointClosureIdeal X x).subschemeι.ker ≤ f.ker
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact reduced_point_closure_ideal_le_ker x f h

/-- The constructed factorization retains the specified actual morphism. -/
theorem reducedPointClosureLift_fac
    {X Y : Scheme.{u}} [IsReduced Y] (x : X) (f : Y ⟶ X)
    (h : Set.range f ⊆ closure {x}) :
    reducedPointClosureLift x f h ≫ reducedPointClosureInclusion X x = f := by
  let : IsClosedImmersion (reducedPointClosureInclusion X x) :=
    reducedPointClosureInclusion_isClosedImmersion X x
  unfold reducedPointClosureLift
  exact IsClosedImmersion.lift_fac _ _ _

end DimensionFourDependence
