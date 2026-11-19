import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-! # Integer scheme orders and regular maximal-ideal bounds

Mathlib assigns integer order zero to the zero rational function. For
regular section bounds we therefore handle the zero section explicitly.
-/

namespace DimensionFourDependence

open AlgebraicGeometry IsDiscreteValuationRing

universe u

set_option maxHeartbeats 1000000

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  (y : X)
  [IsDiscreteValuationRing (X.presheaf.stalk y)]

/-- A regular unit times the nth uniformizer power has actual integer
scheme order n in the scheme's own function field. -/
theorem scheme_order_unit_mul_uniformizer_pow
    (hy : Order.coheight y = 1)
    (π : X.presheaf.stalk y) (hπ : Irreducible π)
    (v : (X.presheaf.stalk y)ˣ) (n : ℕ) :
    X.ord (algebraMap (X.presheaf.stalk y) X.functionField
      ((v : X.presheaf.stalk y) * π ^ n)) y = n := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk y) := krullDimLE_of_coheight_le hy.le
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hy]
  change Multiplicative.toAdd ((Ring.ordFrac (X.presheaf.stalk y)
    (algebraMap (X.presheaf.stalk y) X.functionField
      ((v : X.presheaf.stalk y) * π ^ n))).unzeroD 1) = n
  rw [map_mul, map_pow, map_mul, map_pow,
    Ring.ordFrac_of_isUnit v.isUnit, Ring.ordFrac_irreducible hπ, one_mul]
  change Multiplicative.toAdd ((Multiplicative.ofAdd (1 : ℤ)) ^ n) = n
  simp

/-- For a nonzero regular section, its integer scheme order bound
is exactly membership in the corresponding maximal-ideal power. -/
theorem scheme_regular_integer_order_bound_iff
    (hy : Order.coheight y = 1)
    (z : X.presheaf.stalk y) (hz : z ≠ 0) (a : ℕ) :
    (a : ℤ) ≤ X.ord (algebraMap (X.presheaf.stalk y) X.functionField z) y ↔
      z ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) ^ a := by
  obtain ⟨π, hπ⟩ := exists_irreducible (X.presheaf.stalk y)
  obtain ⟨n, v, rfl⟩ := eq_unit_mul_pow_irreducible hz hπ
  rw [scheme_order_unit_mul_uniformizer_pow y hy π hπ v n]
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd]
  simp [hπ.addVal_pow, AddValuation.map_mul, addVal_eq_zero_of_unit]

/-- Including the zero section explicitly gives the usual regular
order bound for every section, without relying on a junk integer value. -/
theorem scheme_regular_order_bound_iff
    (hy : Order.coheight y = 1)
    (z : X.presheaf.stalk y) (a : ℕ) :
    (z = 0 ∨ (a : ℤ) ≤ X.ord (algebraMap (X.presheaf.stalk y) X.functionField z) y) ↔
      z ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) ^ a := by
  by_cases hz : z = 0
  · simp [hz]
  · simpa only [hz, false_or] using scheme_regular_integer_order_bound_iff y hy z hz a

end DimensionFourDependence
