import DimensionFourDependence.ProjectivePolynomialGermVanishing
import Mathlib.AlgebraicGeometry.FunctionField

/-! # A projective numerator equation constructs its actual vanishing quotient germ -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K]

/-- Original homogeneous vanishing and denominator nonvanishing
construct a regular vanishing fraction germ in the actual source stalk.
Its value is the ratio of the specified pullback sections in the actual
scheme function field. -/
theorem projective_polynomial_quotient_constructs_vanishing_germ
    (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 4) K))
    (y : Y) (a : Fin 4) (ha : X a ∉ (f y).asHomogeneousIdeal)
    (N L : MvPolynomial (Fin 4) K) {D e : ℕ}
    (hN : N.IsHomogeneous D) (hL : L.IsHomogeneous e)
    (hNy : N ∈ (f y).asHomogeneousIdeal) (hLy : L ∉ (f y).asHomogeneousIdeal)
    (d : ℕ) :
    let U := f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X a)
    letI : Nonempty U := ⟨⟨y, ha⟩⟩
    ∃ g : Y.presheaf.stalk y,
      algebraMap (Y.presheaf.stalk y) Y.functionField g =
        Y.germToFunctionField U (projectivePullbackChartPolynomialHom Y f a N) /
          (Y.germToFunctionField U (projectivePullbackChartPolynomialHom Y f a L)) ^ d ∧
      g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  intro U
  letI : Nonempty U := ⟨⟨y, ha⟩⟩
  let n := Y.presheaf.germ U y ha (projectivePullbackChartPolynomialHom Y f a N)
  let l := Y.presheaf.germ U y ha (projectivePullbackChartPolynomialHom Y f a L)
  have hn : n ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
    (projective_pullback_polynomial_germ_mem_maximal_iff Y f y a ha N hN).mpr hNy
  have hl : l ∉ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
    exact fun h => hLy ((projective_pullback_polynomial_germ_mem_maximal_iff
      Y f y a ha L hL).mp h)
  have hunit : IsUnit l := IsLocalRing.notMem_maximalIdeal.mp hl
  let g := n * ((↑(hunit.unit⁻¹) : Y.presheaf.stalk y) ^ d)
  have hl0 : algebraMap (Y.presheaf.stalk y) Y.functionField l ≠ 0 :=
    (hunit.map (algebraMap (Y.presheaf.stalk y) Y.functionField)).ne_zero
  refine ⟨g, ?_, (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).mul_mem_right _ hn⟩
  have hnval := Y.algebraMap_germ_eq_germToFunctionField ha
    (projectivePullbackChartPolynomialHom Y f a N)
  have hlval := Y.algebraMap_germ_eq_germToFunctionField ha
    (projectivePullbackChartPolynomialHom Y f a L)
  rw [← hnval, ← hlval]
  apply (eq_div_iff (pow_ne_zero d hl0)).mpr
  rw [← map_pow, ← map_mul]
  apply congrArg (algebraMap (Y.presheaf.stalk y) Y.functionField)
  change (n * (↑(hunit.unit⁻¹) : Y.presheaf.stalk y) ^ d) * l ^ d = n
  rw [mul_assoc, ← mul_pow]
  have hc : (↑(hunit.unit⁻¹) : Y.presheaf.stalk y) * l = 1 := by
    calc
      (↑(hunit.unit⁻¹) : Y.presheaf.stalk y) * l =
          (↑(hunit.unit⁻¹) : Y.presheaf.stalk y) * ↑hunit.unit :=
        congrArg (fun t => (↑(hunit.unit⁻¹) : Y.presheaf.stalk y) * t) hunit.unit_spec.symm
      _ = 1 := Units.inv_mul hunit.unit
  rw [hc, one_pow, mul_one]

end DimensionFourDependence
