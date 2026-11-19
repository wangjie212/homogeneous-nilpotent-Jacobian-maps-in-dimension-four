import DimensionFourDependence.QuinticAuxiliaryFlowIdentities

/-! # The parameter sign under the involution in (6.21) -/

namespace DimensionFourDependence.Quintic

variable {R : Type*} [CommRing R]

def auxiliaryInvariantT (a c : R) (s : AuxiliaryState R) : AuxiliaryState R :=
  auxiliaryT a (c * auxiliaryQ a s) s

def auxiliaryInvariantR (a c : R) (s : AuxiliaryState R) : AuxiliaryState R :=
  auxiliaryR a (c * auxiliaryQ a s) s

/-- Evaluation after the involution changes the sign of the parameter.
This cancels the sign in the inverse T-flow. -/
theorem auxiliaryInvolution_conjugates_invariant_T_inv (a c : R) (s : AuxiliaryState R) :
    auxiliaryInvolution (auxiliaryInvariantT a (-c) (auxiliaryInvolution s)) =
      auxiliaryInvariantR a c s := by
  unfold auxiliaryInvariantT auxiliaryInvariantR
  rw [auxiliaryInvolution_negates_Q, neg_mul_neg, auxiliaryInvolution_conjugates_T]

/-- The commutator in (6.21) is the product of the two forward flows. -/
theorem auxiliary_invariant_flow_involution_product (a c : R) (s : AuxiliaryState R) :
    auxiliaryInvariantT a c (auxiliaryInvolution (auxiliaryInvariantT a (-c) (auxiliaryInvolution s))) =
      ⟨s.p - 2 * (s.u - s.v) * (c * auxiliaryQ a s),
        s.v + a * (c * auxiliaryQ a s), s.u + a * (c * auxiliaryQ a s)⟩ := by
  rw [auxiliaryInvolution_conjugates_invariant_T_inv]
  unfold auxiliaryInvariantT auxiliaryInvariantR
  rw [auxiliaryR_preserves_Q, auxiliaryT_comp_auxiliaryR]

end DimensionFourDependence.Quintic
