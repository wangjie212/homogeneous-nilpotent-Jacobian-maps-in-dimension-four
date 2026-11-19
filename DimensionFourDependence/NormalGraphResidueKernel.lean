import DimensionFourDependence.IntegralLevelReciprocal
import Mathlib.Algebra.Polynomial.Roots

/-! # Normal zero-pole intersections have a free polynomial parameter in the graph fiber -/

namespace DimensionFourDependence

open Polynomial

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {k R : Type*} [Field k] [Infinite k] [CommRing R] [IsLocalRing R] [Algebra k R]

/-- A polynomial nonzero in the residue field has a unit value at
some scalar of the original infinite coefficient field. No equality
between the coefficient field and the residue field is required. -/
theorem nonzero_residue_polynomial_constructs_scalar_unit_value
    (P : Polynomial R) (hP : P.map (IsLocalRing.residue R) ≠ 0) :
    ∃ c : k, IsUnit (P.eval (algebraMap k R c)) := by
  let ι : k →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp (algebraMap k R)
  obtain ⟨c, hc⟩ : ∃ c : k, (P.map (IsLocalRing.residue R)).eval (ι c) ≠ 0 := by
    by_contra hn
    push Not at hn
    have hfinite : (Set.range ι).Finite := (Polynomial.finite_setOfPred_isRoot hP).subset (by
      rintro _ ⟨c, rfl⟩
      exact hn c)
    exact (Set.infinite_range_of_injective ι.injective) hfinite
  have hvalue : IsLocalRing.residue R (P.eval (algebraMap k R c)) ≠ 0 := by
    rw [← Polynomial.eval₂_at_apply (IsLocalRing.residue R) (algebraMap k R c),
      Polynomial.eval₂_eq_eval_map]
    exact hc
  exact ⟨c, IsLocalRing.notMem_maximalIdeal.mp
    (fun h => hvalue ((IsLocalRing.residue_eq_zero_iff _).mpr h))⟩

variable {F : Type*} [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F] [IsIntegrallyClosed R]

/-- If no scalar-level reciprocal is regular at the normal local
point, every actual polynomial relation for f has zero residue
polynomial. Thus its graph imposes no residue equation on the level
parameter at the original closed point. -/
theorem normal_graph_relation_residue_polynomial_eq_zero
    (f : F)
    (hrecip : ∀ c : k, ¬IsLocalization.IsInteger R
      ((f - algebraMap R F (algebraMap k R c))⁻¹))
    (P : Polynomial R) (hroot : aeval f P = 0) :
    P.map (IsLocalRing.residue R) = 0 := by
  by_contra hmap
  obtain ⟨c, hc⟩ := nonzero_residue_polynomial_constructs_scalar_unit_value (k := k) P hmap
  exact hrecip c (normal_polynomial_relation_unit_value_regular_level_reciprocal P f
    (algebraMap k R c) hroot hc)

/-- The entire actual polynomial evaluation kernel lies below the
coefficientwise residue kernel, keeping the polynomial variable free. -/
theorem normal_graph_kernel_le_residue_polynomial_kernel
    (f : F)
    (hrecip : ∀ c : k, ¬IsLocalization.IsInteger R
      ((f - algebraMap R F (algebraMap k R c))⁻¹)) :
    RingHom.ker (Polynomial.aeval f).toRingHom ≤
      RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)) := by
  intro P hP
  exact normal_graph_relation_residue_polynomial_eq_zero (k := k) f hrecip P hP

/-- In coefficient language, every actual relation for f vanishes
at the original local closed point in every coefficient. -/
theorem normal_graph_relation_coeff_mem_maximal
    (f : F)
    (hrecip : ∀ c : k, ¬IsLocalization.IsInteger R
      ((f - algebraMap R F (algebraMap k R c))⁻¹))
    (P : Polynomial R) (hroot : aeval f P = 0) (i : ℕ) :
    P.coeff i ∈ IsLocalRing.maximalIdeal R := by
  have he := congrArg (fun Q : Polynomial (IsLocalRing.ResidueField R) => Q.coeff i)
    (normal_graph_relation_residue_polynomial_eq_zero (k := k) f hrecip P hroot)
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at he
  exact (IsLocalRing.residue_eq_zero_iff _).mp he

include k

/-- A zero branch and pole branch through the actual normal local
point therefore make its rational graph parameter completely free in
the residue fiber. No generic scalar is supplied or specialized. -/
theorem zero_pole_graph_kernel_le_residue_polynomial_kernel
    (f : F) (V₀ Vinf : ValuationSubring F)
    (hR₀ : ∀ a : R, algebraMap R F a ∈ V₀)
    (hRinf : ∀ a : R, algebraMap R F a ∈ Vinf)
    (hzero : f ∈ V₀.nonunits) (hpole : f⁻¹ ∈ Vinf.nonunits) (hf : f ≠ 0) :
    RingHom.ker (Polynomial.aeval f).toRingHom ≤
      RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)) :=
  normal_graph_kernel_le_residue_polynomial_kernel (k := k) f
    (fun c => zero_pole_level_reciprocal_not_isInteger R f (algebraMap k R c)
      V₀ Vinf hR₀ hRinf hzero hpole hf)

end DimensionFourDependence
