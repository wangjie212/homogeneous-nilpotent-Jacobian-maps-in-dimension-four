import DimensionFourDependence.QuinticParameterShifting
import DimensionFourDependence.QuinticAuxiliaryGrouping

/-! # Substitution through the explicit states in the quintic factorization -/

namespace DimensionFourDependence.Quintic

variable {R S : Type*} [CommRing R] [CommRing S]

def ActiveState.map (s : ActiveState R) (f : R →+* S) : ActiveState S :=
  ⟨f s.x, f s.y, f s.z⟩

def AuxiliaryState.map (s : AuxiliaryState R) (f : R →+* S) : AuxiliaryState S :=
  ⟨f s.p, f s.v, f s.u⟩

theorem activeState_map_comp {T : Type*} [CommRing T]
    (s : ActiveState R) (f : R →+* S) (g : S →+* T) :
    s.map (g.comp f) = (s.map f).map g := rfl

theorem auxiliaryState_map_comp {T : Type*} [CommRing T]
    (s : AuxiliaryState R) (f : R →+* S) (g : S →+* T) :
    s.map (g.comp f) = (s.map f).map g := rfl

theorem map_secondInvariant (f : R →+* S) (half t : R) (s : ActiveState R) :
    f (secondInvariant half t s) = secondInvariant (f half) (f t) (s.map f) := by
  simp only [ActiveState.map, secondInvariant, omega, map_sub, map_mul,
    map_add, map_pow, map_one, map_ofNat]

theorem map_secondLiftFlow (f : R →+* S) (half t h : R) (s : ActiveState R) :
    (secondLiftFlow half t h s).map f = secondLiftFlow (f half) (f t) (f h) (s.map f) := by
  simp only [ActiveState.map, secondLiftFlow, omega, map_sub, map_mul, map_add,
    map_pow, map_one, map_ofNat]

theorem map_parameterShift (f : R →+* S) (t k : R) (s : ActiveState R) :
    (parameterShift t k s).map f = parameterShift (f t) (f k) (s.map f) := by
  simp only [ActiveState.map, parameterShift, map_add, map_mul, map_sub]

theorem map_auxiliaryQ (f : R →+* S) (a : R) (s : AuxiliaryState R) :
    f (auxiliaryQ a s) = auxiliaryQ (f a) (s.map f) := by
  simp only [auxiliaryQ, AuxiliaryState.map, map_add, map_sub, map_pow, map_mul]

theorem map_auxiliaryq (f : R →+* S) (a : R) (s : AuxiliaryState R) :
    f (auxiliaryq a s) = auxiliaryq (f a) (s.map f) := by
  simp only [auxiliaryq, AuxiliaryState.map, map_sub, map_pow, map_mul]

theorem map_auxiliaryT (f : R →+* S) (a h : R) (s : AuxiliaryState R) :
    (auxiliaryT a h s).map f = auxiliaryT (f a) (f h) (s.map f) := by
  simp only [auxiliaryT, AuxiliaryState.map, map_add, map_mul, map_pow, map_ofNat]

theorem map_auxiliaryInvolution (f : R →+* S) (s : AuxiliaryState R) :
    (auxiliaryInvolution s).map f = auxiliaryInvolution (s.map f) := by
  simp only [auxiliaryInvolution, AuxiliaryState.map, map_neg]

theorem map_quinticAuxiliaryState (f : R →+* S) (half t : R) (s : ActiveState R) :
    (quinticAuxiliaryState half s.x s.y s.z t).map f =
      quinticAuxiliaryState (f half) (f s.x) (f s.y) (f s.z) (f t) := by
  simp only [quinticAuxiliaryState, AuxiliaryState.map, coordinateP, coordinateV, coordinateW,
    coordinateU, map_add, map_mul, map_sub]

end DimensionFourDependence.Quintic
