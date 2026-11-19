import DimensionFourDependence.SeparatingZeroDivisors
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Specializing actual germs constructs two height-one local branches -/

namespace DimensionFourDependence

open AlgebraicGeometry CategoryTheory

universe u

variable (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y]

/-- A numerator zero and denominator unit on a specializing branch,
and a denominator zero at its specialization, construct distinct height-one
branches in that same specialization stalk. The quotient germ is formed
in its actual scheme function field. -/
theorem specialization_germs_construct_height_one_local_branches
    (x z : Y) (hxz : x ⤳ z) (U : Y.Opens) (hz : z ∈ U)
    (n l : Γ(Y, U))
    (hn0 : Y.presheaf.germ U z hz n ≠ 0)
    (hnx : Y.presheaf.germ U x (hxz.mem_open U.isOpen hz) n ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
    (hlx : IsUnit (Y.presheaf.germ U x (hxz.mem_open U.isOpen hz) l))
    (hlz : Y.presheaf.germ U z hz l ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z))
    (d : ℕ) :
    ∃ q₀ qL : PrimeSpectrum (Y.presheaf.stalk z),
      q₀.asIdeal.height = 1 ∧ qL.asIdeal.height = 1 ∧ q₀ ≠ qL ∧
      Y.presheaf.germ U z hz n ∈ q₀.asIdeal ∧
      Y.presheaf.germ U z hz l ∉ q₀.asIdeal ∧
      Y.presheaf.germ U z hz l ∈ qL.asIdeal ∧
      ∃ g : fractionPrimeLocalAlgebra (F := Y.functionField) (Y.presheaf.stalk z) q₀.asIdeal,
        (g : Y.functionField) =
          algebraMap (Y.presheaf.stalk z) Y.functionField (Y.presheaf.germ U z hz n) /
            (algebraMap (Y.presheaf.stalk z) Y.functionField (Y.presheaf.germ U z hz l)) ^ d ∧
        g ∈ IsLocalRing.maximalIdeal
          (fractionPrimeLocalAlgebra (F := Y.functionField) (Y.presheaf.stalk z) q₀.asIdeal) := by
  let φ : Y.presheaf.stalk z →+* Y.presheaf.stalk x :=
    (Y.presheaf.stalkSpecializes hxz).hom
  have hmap (v : Γ(Y, U)) : φ (Y.presheaf.germ U z hz v) =
      Y.presheaf.germ U x (hxz.mem_open U.isOpen hz) v :=
    ConcreteCategory.congr_hom (Y.presheaf.germ_stalkSpecializes hz hxz) v
  apply local_map_constructs_distinct_zero_and_denominator_divisors
    (F := Y.functionField) φ _ _ hn0 ?_ ?_ hlz d
  · rw [hmap]
    exact hnx
  · rw [hmap]
    exact hlx

end DimensionFourDependence
