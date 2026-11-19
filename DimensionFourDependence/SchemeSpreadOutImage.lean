import DimensionFourDependence.GlobalDivisorImagePrime

/-! # The source image of a spread-out closure

Taking closure in a parameter model does not alter the closure of the
source image. This connects a family's actual source-divisor density
with the source image of its original generic curve.
-/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

/-- A generic curve and its closure in an actual parameter model have
the same closed source image through a compatible scheme projection. -/
theorem scheme_spread_out_source_image_closure
    {X Y S : Scheme.{u}} (i : Y ⟶ S) (p : S ⟶ X) (f : Y ⟶ X)
    (h : i ≫ p = f) (Z : Set Y) :
    closure (p '' closure (i '' Z)) = closure (f '' Z) := by
  rw [closure_image_closure p.continuous, ← Set.image_comp]
  have heq : p ∘ i = f := by
    funext y
    exact congrArg (fun k : Y ⟶ X => k y) h
  rw [heq]

/-- The actual generic point of a prime curve maps to the generic
point of its spread-out closure, without choosing an affine prime. -/
theorem scheme_spread_out_generic_point
    {Y S : Scheme.{u}} (i : Y ⟶ S) (Z : Set Y)
    (hZ : IsIrreducible Z) (hZclosed : IsClosed Z) :
    IsGenericPoint (i hZ.genericPoint) (closure (i '' Z)) := by
  exact (hZ.isGenericPoint_genericPoint hZclosed).image i.continuous

end DimensionFourDependence
