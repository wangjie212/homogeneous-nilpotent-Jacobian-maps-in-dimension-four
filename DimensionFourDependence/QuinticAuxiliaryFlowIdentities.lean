import DimensionFourDependence.QuinticPolynomialCoordinates

/-! # The two auxiliary polynomial flows and their involution -/

namespace DimensionFourDependence.Quintic

structure AuxiliaryState (R : Type*) where
  p : R
  v : R
  u : R

variable {R : Type*} [CommRing R]

def auxiliaryQ (a : R) (s : AuxiliaryState R) : R := a * s.p - s.v ^ 2 + s.u ^ 2

def auxiliaryT (a h : R) (s : AuxiliaryState R) : AuxiliaryState R :=
  ⟨s.p + 2 * s.v * h + a * h ^ 2, s.v + a * h, s.u⟩

def auxiliaryR (a h : R) (s : AuxiliaryState R) : AuxiliaryState R :=
  ⟨s.p - 2 * s.u * h - a * h ^ 2, s.v, s.u + a * h⟩

def auxiliaryInvolution (s : AuxiliaryState R) : AuxiliaryState R := ⟨-s.p, s.u, s.v⟩

theorem auxiliaryT_preserves_Q (a h : R) (s : AuxiliaryState R) :
    auxiliaryQ a (auxiliaryT a h s) = auxiliaryQ a s := by
  simp only [auxiliaryT, auxiliaryQ]
  ring

theorem auxiliaryR_preserves_Q (a h : R) (s : AuxiliaryState R) :
    auxiliaryQ a (auxiliaryR a h s) = auxiliaryQ a s := by
  simp only [auxiliaryR, auxiliaryQ]
  ring

theorem auxiliaryT_comp_parameter_add (a h k : R) (s : AuxiliaryState R) :
    auxiliaryT a h (auxiliaryT a k s) = auxiliaryT a (h + k) s := by
  unfold auxiliaryT
  congr 1 <;> ring

theorem auxiliaryT_comp_auxiliaryR (a h : R) (s : AuxiliaryState R) :
    auxiliaryT a h (auxiliaryR a h s) =
      ⟨s.p - 2 * (s.u - s.v) * h, s.v + a * h, s.u + a * h⟩ := by
  unfold auxiliaryT auxiliaryR
  congr 1 <;> ring

theorem auxiliaryInvolution_negates_Q (a : R) (s : AuxiliaryState R) :
    auxiliaryQ a (auxiliaryInvolution s) = -auxiliaryQ a s := by
  simp only [auxiliaryQ, auxiliaryInvolution]
  ring

theorem auxiliaryInvolution_conjugates_T (a h : R) (s : AuxiliaryState R) :
    auxiliaryInvolution (auxiliaryT a h (auxiliaryInvolution s)) = auxiliaryR a h s := by
  unfold auxiliaryInvolution auxiliaryT auxiliaryR
  congr 1 <;> ring

end DimensionFourDependence.Quintic
