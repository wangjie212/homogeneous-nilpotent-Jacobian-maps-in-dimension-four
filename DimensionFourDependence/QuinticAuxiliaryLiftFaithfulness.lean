import DimensionFourDependence.QuinticBasicLiftTameness

/-! # The auxiliary coordinates determine an actual fixed-t automorphism -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1200000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "x" => (X 0 : R₄)
local notation "y" => (X 1 : R₄)
local notation "z" => (X 2 : R₄)
local notation "t" => (X 3 : R₄)
local notation "half" => (C (2 : K)⁻¹ : R₄)
local notation "b" => (quinticAuxiliaryState half x y z t)

/-- Multiplication by the common nonzero polynomial t can be canceled,
so agreement on the auxiliary tuple is enough to identify automorphisms
in the original polynomial ring. -/
theorem quintic_automorphisms_eq_of_auxiliary_images
    (E F : Aut₄) (hEt : E t = t) (hFt : F t = t)
    (h : (b).map E.toRingHom = (b).map F.toRingHom) : E = F := by
  rw [quintic_auxiliary_state_after_substitution E (E x) (E y) (E z) rfl rfl rfl hEt,
    quintic_auxiliary_state_after_substitution F (F x) (F y) (F z) rfl rfl rfl hFt] at h
  have hp := congrArg AuxiliaryState.p h
  have hv := congrArg AuxiliaryState.v h
  have hu := congrArg AuxiliaryState.u h
  obtain ⟨hx, hy, hz⟩ := quintic_auxiliary_coordinates_injective half t
    (E x) (E y) (E z) (F x) (F y) (F z) original_quintic_half_identity (X_ne_zero 3) hp hv hu
  have he : E.toAlgHom = F.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
    · exact hEt.trans hFt.symm
  apply AlgEquiv.ext
  exact AlgHom.congr_fun he

theorem substitute_quintic_invariant_flow (E : Aut₄) (hEt : E t = t) (η scale : K)
    (w : AuxiliaryState R₄) :
    (auxiliaryInvariantT (C η * t) (half * (C scale * t ^ 2)) w).map E.toRingHom =
      auxiliaryInvariantT (C η * t) (half * (C scale * t ^ 2)) (w.map E.toRingHom) := by
  have ht : E.toRingHom t = t := hEt
  have hC (c : K) : E.toRingHom (C c : R₄) = C c := E.commutes c
  simp only [auxiliaryInvariantT, map_auxiliaryT, map_auxiliaryQ,
    map_mul, map_pow, ht, hC]

end DimensionFourDependence.Quintic
