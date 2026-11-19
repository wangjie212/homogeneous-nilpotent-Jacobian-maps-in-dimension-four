import DimensionFourDependence.IntrinsicDivisorPullback
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.RingTheory.KrullDimension.PID

/-! # Intrinsic stalk comparisons give scheme function-field orders

The comparison is expressed using the schemes' actual function fields
and Mathlib's integer order of vanishing at codimension-one points.
-/

namespace DimensionFourDependence

open AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual geometric pullback extends to the schemes' function
fields and preserves their integer orders of vanishing. -/
noncomputable def SchemeDivisorPullbackComparison
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] (f : Y ⟶ X) (y : Y) : Prop :=
  ∃ _hx : Order.coheight (f y) = 1, ∃ _hy : Order.coheight y = 1,
    ∃ j : X.functionField →+* Y.functionField,
      (∀ z : X.presheaf.stalk (f y),
        j (algebraMap (X.presheaf.stalk (f y)) X.functionField z) =
          algebraMap (Y.presheaf.stalk y) Y.functionField (f.stalkMap y z)) ∧
      ∀ x : X.functionField, X.ord x (f y) = Y.ord (j x) y

/-- The intrinsic comparison supplies the actual scheme function-field
pullback, target codimension one, and equality of integer divisor orders. -/
theorem intrinsic_divisor_pullback_scheme_orders
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] (f : Y ⟶ X) (y : Y)
    (hx : Order.coheight (f y) = 1)
    (h : IntrinsicDivisorPullbackComparison (f.stalkMap y).hom) :
    SchemeDivisorPullbackComparison f y := by
  let S := X.presheaf.stalk (f y)
  let A := Y.presheaf.stalk y
  obtain ⟨hS, hA, hDVR, hframed, hregular⟩ := h
  let : IsDiscreteValuationRing S := hDVR
  obtain ⟨hDVRA, j, hj, hv, hframes⟩ := hframed
  let : IsDiscreteValuationRing A := hDVRA
  let : Algebra A (FractionRing A) := OreLocalization.instAlgebra
  have hcanonical : CanonicalRationalSourceOrderComparison
      (O := S) (A := A) (F := FractionRing S) (f.stalkMap y).hom := by
    refine ⟨hDVRA, j, ?_, hv⟩
    intro z
    exact hj z
  have hfunction : CanonicalRationalSourceOrderComparison
      (O := S) (A := A) (F := X.functionField) (f.stalkMap y).hom :=
    canonical_rational_comparison_change_fraction_field _ hcanonical
  obtain ⟨hDVRA', k, hk, hw⟩ := hfunction
  let : IsDiscreteValuationRing A := hDVRA'
  let b : FractionRing A ≃ₐ[A] Y.functionField :=
    IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A) Y.functionField
  have hy : Order.coheight y = 1 := by
    have hdim := IsPrincipalIdealRing.ringKrullDim_eq_one A (IsDiscreteValuationRing.not_isField A)
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    exact_mod_cast hdim
  refine ⟨hx, hy, b.toRingHom.comp k, ?_, ?_⟩
  · intro z
    change b (k (algebraMap S X.functionField z)) = _
    rw [hk, b.commutes]
  · intro x
    have hval := (hw x).trans (divisor_valuation_fraction_field_map
      (IsDiscreteValuationRing.maximalIdeal A) b.toRingHom b.commutes (k x))
    change (IsDiscreteValuationRing.maximalIdeal S).valuation X.functionField x =
      (IsDiscreteValuationRing.maximalIdeal A).valuation Y.functionField (b (k x)) at hval
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx,
      Scheme.ord_eq_ordHom_of_coheight_eq_one hy]
    change Multiplicative.toAdd ((Ring.ordFrac S x).unzeroD 1) =
      Multiplicative.toAdd ((Ring.ordFrac A (b (k x))).unzeroD 1)
    rw [Ring.ordFrac_eq_valuation_inv, Ring.ordFrac_eq_valuation_inv, hval]

/-- Values of the entire actual source stalk uniquely determine the
pullback between the schemes' actual function fields. -/
theorem scheme_source_function_field_pullback_unique
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (y : Y) (j k : X.functionField →+* Y.functionField)
    (hj : ∀ z : X.presheaf.stalk (f y),
      j (algebraMap (X.presheaf.stalk (f y)) X.functionField z) =
        algebraMap (Y.presheaf.stalk y) Y.functionField (f.stalkMap y z))
    (hk : ∀ z : X.presheaf.stalk (f y),
      k (algebraMap (X.presheaf.stalk (f y)) X.functionField z) =
        algebraMap (Y.presheaf.stalk y) Y.functionField (f.stalkMap y z)) : j = k := by
  apply IsFractionRing.ringHom_ext (A := X.presheaf.stalk (f y))
  intro z
  exact (hj z).trans (hk z).symm

/-- Integer scheme orders of a rational section are unchanged by
every regular source-stalk transition unit in its chosen local frame. -/
theorem scheme_source_rational_section_frame_order
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (y : Y) (hx : Order.coheight (f y) = 1)
    (j : X.functionField →+* Y.functionField)
    (horder : ∀ x : X.functionField, X.ord x (f y) = Y.ord (j x) y)
    (u : (X.presheaf.stalk (f y))ˣ) (x : X.functionField) :
    Y.ord (j (algebraMap (X.presheaf.stalk (f y)) X.functionField (u : X.presheaf.stalk (f y)) * x)) y =
      X.ord x (f y) := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk (f y)) := krullDimLE_of_coheight_le hx.le
  rw [← horder, Scheme.ord_eq_ordHom_of_coheight_eq_one hx,
    Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  change Multiplicative.toAdd ((Ring.ordFrac (X.presheaf.stalk (f y))
      (algebraMap (X.presheaf.stalk (f y)) X.functionField (u : X.presheaf.stalk (f y)) * x)).unzeroD 1) =
    Multiplicative.toAdd ((Ring.ordFrac (X.presheaf.stalk (f y)) x).unzeroD 1)
  rw [map_mul, Ring.ordFrac_of_isUnit u.isUnit, one_mul]

end DimensionFourDependence
