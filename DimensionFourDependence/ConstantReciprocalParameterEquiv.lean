import DimensionFourDependence.PrimitiveRationalVector
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Constant reciprocal changes are actual rational-field equivalences

The change u=1/(t-a) remains transcendental and generates the same entire
rational function field: t=a+1/u. It therefore defines a K-algebra
automorphism, retaining the full field rather than only a parameter value.
-/

namespace DimensionFourDependence

variable {K : Type*} [Field K]

/-- A constant translated reciprocal of the rational parameter is
transcendental over the original coefficient field. -/
theorem constant_reciprocal_parameter_transcendental (a : K) :
    Transcendental K ((RatFunc.X - algebraMap K (RatFunc K) a)⁻¹ : RatFunc K) := by
  intro h
  have hh := h.inv.add (isAlgebraic_algebraMap (A := RatFunc K) a)
  apply RatFunc.transcendental_X (K := K)
  convert hh using 1
  simp only [inv_inv]
  ring

/-- The translated reciprocal generates the whole original rational
function field, since the original variable is a+1/u. -/
theorem constant_reciprocal_parameter_adjoin_eq_top (a : K) :
    IntermediateField.adjoin K {((RatFunc.X - algebraMap K (RatFunc K) a)⁻¹ : RatFunc K)} = ⊤ := by
  let J := IntermediateField.adjoin K {((RatFunc.X - algebraMap K (RatFunc K) a)⁻¹ : RatFunc K)}
  have hu : ((RatFunc.X - algebraMap K (RatFunc K) a)⁻¹ : RatFunc K) ∈ J :=
    IntermediateField.subset_adjoin K _ rfl
  have hX : (RatFunc.X : RatFunc K) ∈ J := by
    have h := J.add_mem (J.inv_mem hu) (J.algebraMap_mem a)
    simpa only [inv_inv, sub_add_cancel] using h
  have hle : (⊤ : IntermediateField K (RatFunc K)) ≤ J := by
    rw [← RatFunc.adjoin_X]
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hX)
  exact top_unique hle

/-- The actual K-algebra automorphism sending t to 1/(t-a). -/
noncomputable def constantReciprocalParameterEquiv (a : K) : RatFunc K ≃ₐ[K] RatFunc K :=
  (RatFunc.algEquivOfTranscendental
    ((RatFunc.X - algebraMap K (RatFunc K) a)⁻¹ : RatFunc K)
    (constant_reciprocal_parameter_transcendental a)).trans
    ((IntermediateField.equivOfEq (constant_reciprocal_parameter_adjoin_eq_top a)).trans
      IntermediateField.topEquiv)

/-- This field equivalence has exactly the prescribed reciprocal
value on the original rational parameter. -/
theorem constantReciprocalParameterEquiv_X (a : K) :
    constantReciprocalParameterEquiv a RatFunc.X =
      ((RatFunc.X - algebraMap K (RatFunc K) a)⁻¹ : RatFunc K) := by
  change ((RatFunc.algEquivOfTranscendental _ (constant_reciprocal_parameter_transcendental a))
    RatFunc.X : RatFunc K) = _
  exact RatFunc.algEquivOfTranscendental_X _ _

end DimensionFourDependence
