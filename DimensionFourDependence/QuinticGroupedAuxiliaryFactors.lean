import DimensionFourDependence.QuinticStateSubstitution

/-! # The two grouped auxiliary factors in equation (6.27) -/

namespace DimensionFourDependence.Quintic

variable {R : Type*} [CommRing R]

def groupedAuxiliaryFirst (a half k : R) (s : AuxiliaryState R) : AuxiliaryState R :=
  let r := auxiliaryA a half s
  let h := k * r.u
  auxiliaryA a (-half) (auxiliaryPShift (2 * r.v * h - a * h ^ 2) r)

def groupedAuxiliarySecond (a half k : R) (s : AuxiliaryState R) : AuxiliaryState R :=
  let r := auxiliaryA a half s
  auxiliaryA a (-half) (auxiliaryVShift (a * (k * r.u)) r)

theorem groupedAuxiliaryFirst_coordinates (a half k : R) (s : AuxiliaryState R) :
    let r := s.u + half * auxiliaryq a s
    let h := k * r
    let f := 2 * s.v * h - a * h ^ 2
    groupedAuxiliaryFirst a half k s = ⟨s.p + f, s.v, s.u - half * a * f⟩ :=
  auxiliaryA_conjugates_p_shift a half _ s

theorem groupedAuxiliarySecond_coordinates (a half k : R) (s : AuxiliaryState R) :
    let r := s.u + half * auxiliaryq a s
    let c := a * (k * r)
    groupedAuxiliarySecond a half k s =
      ⟨s.p, s.v + c, s.u + half * (2 * s.v * c + c ^ 2)⟩ :=
  auxiliaryA_conjugates_v_shift a half _ s

/-- Grouping before lifting permits only the two conjugated factors
to be constructed over the original polynomial ring. -/
theorem groupedAuxiliaryFirst_comp_second (a half k : R) (s : AuxiliaryState R) :
    groupedAuxiliaryFirst a half k (groupedAuxiliarySecond a half k s) =
      auxiliaryA a (-half) (auxiliaryT a (k * (auxiliaryA a half s).u) (auxiliaryA a half s)) := by
  let r := auxiliaryA a half s
  let h := k * r.u
  let w := auxiliaryVShift (a * h) r
  have hw : auxiliaryA a half (groupedAuxiliarySecond a half k s) = w :=
    auxiliaryA_comp_inv a half w
  have hu : w.u = r.u := rfl
  unfold groupedAuxiliaryFirst
  rw [hw]
  dsimp only
  rw [hu]
  change auxiliaryA a (-half) (auxiliaryPShift (2 * w.v * h - a * h ^ 2) w) =
    auxiliaryA a (-half) (auxiliaryT a h r)
  rw [auxiliaryT_eq_auxiliary_shifts]

theorem map_groupedAuxiliaryFirst {S : Type*} [CommRing S] (f : R →+* S)
    (a half k : R) (s : AuxiliaryState R) :
    (groupedAuxiliaryFirst a half k s).map f =
      groupedAuxiliaryFirst (f a) (f half) (f k) (s.map f) := by
  simp only [groupedAuxiliaryFirst_coordinates, AuxiliaryState.map, map_auxiliaryq,
    map_add, map_sub, map_mul, map_pow, map_ofNat]

theorem map_groupedAuxiliarySecond {S : Type*} [CommRing S] (f : R →+* S)
    (a half k : R) (s : AuxiliaryState R) :
    (groupedAuxiliarySecond a half k s).map f =
      groupedAuxiliarySecond (f a) (f half) (f k) (s.map f) := by
  simp only [groupedAuxiliarySecond_coordinates, AuxiliaryState.map, map_auxiliaryq,
    map_add, map_mul, map_pow, map_ofNat]

end DimensionFourDependence.Quintic
