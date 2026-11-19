import DimensionFourDependence.QuinticInvariantFlowSign

/-! # Grouping the auxiliary flow factors before lifting, (6.26)–(6.27) -/

namespace DimensionFourDependence.Quintic

variable {R : Type*} [CommRing R]

def auxiliaryq (a : R) (s : AuxiliaryState R) : R := a * s.p - s.v ^ 2

def auxiliaryA (a h : R) (s : AuxiliaryState R) : AuxiliaryState R :=
  ⟨s.p, s.v, s.u + h * auxiliaryq a s⟩

def auxiliaryPShift (f : R) (s : AuxiliaryState R) : AuxiliaryState R :=
  ⟨s.p + f, s.v, s.u⟩

def auxiliaryVShift (c : R) (s : AuxiliaryState R) : AuxiliaryState R :=
  ⟨s.p, s.v + c, s.u⟩

theorem auxiliaryT_preserves_q (a h : R) (s : AuxiliaryState R) :
    auxiliaryq a (auxiliaryT a h s) = auxiliaryq a s := by
  simp only [auxiliaryq, auxiliaryT]
  ring

theorem auxiliaryA_comp_inv (a h : R) (s : AuxiliaryState R) :
    auxiliaryA a h (auxiliaryA a (-h) s) = s := by
  cases s
  unfold auxiliaryA auxiliaryq
  congr 1 <;> ring

theorem auxiliaryT_eq_auxiliary_shifts (a h : R) (s : AuxiliaryState R) :
    auxiliaryT a h s =
      let s' := auxiliaryVShift (a * h) s
      auxiliaryPShift (2 * s'.v * h - a * h ^ 2) s' := by
  unfold auxiliaryT auxiliaryPShift auxiliaryVShift
  congr 1 <;> ring

/-- The first grouped conjugate changes the auxiliary p-coordinate
and compensates by the exact change of q in the u-coordinate. -/
theorem auxiliaryA_conjugates_p_shift (a half f : R) (s : AuxiliaryState R) :
    auxiliaryA a (-half) (auxiliaryPShift f (auxiliaryA a half s)) =
      ⟨s.p + f, s.v, s.u - half * a * f⟩ := by
  unfold auxiliaryA auxiliaryPShift auxiliaryq
  congr 1 <;> ring

/-- The second grouped conjugate changes the auxiliary v-coordinate
and compensates by the exact change of q in the u-coordinate. -/
theorem auxiliaryA_conjugates_v_shift (a half c : R) (s : AuxiliaryState R) :
    auxiliaryA a (-half) (auxiliaryVShift c (auxiliaryA a half s)) =
      ⟨s.p, s.v + c, s.u + half * (2 * s.v * c + c ^ 2)⟩ := by
  unfold auxiliaryA auxiliaryVShift auxiliaryq
  congr 1 <;> ring

theorem auxiliaryA_conjugates_T_linear_auxiliary_parameter (a half k : R) (s : AuxiliaryState R) :
    auxiliaryA a (-half)
        (auxiliaryT a (k * (auxiliaryA a half s).u) (auxiliaryA a half s)) =
      auxiliaryT a (k * (s.u + half * auxiliaryq a s)) s := by
  let h := k * (s.u + half * auxiliaryq a s)
  have he : k * (auxiliaryA a half s).u = h := rfl
  rw [he]
  have hq : auxiliaryq a (auxiliaryA a half s) = auxiliaryq a s := rfl
  change ⟨(auxiliaryT a h (auxiliaryA a half s)).p, (auxiliaryT a h (auxiliaryA a half s)).v,
      (auxiliaryT a h (auxiliaryA a half s)).u + -half * auxiliaryq a (auxiliaryT a h (auxiliaryA a half s))⟩ =
      auxiliaryT a h s
  rw [auxiliaryT_preserves_q, hq]
  unfold auxiliaryT auxiliaryA
  congr 1 <;> ring

/-- Equation (6.26), with the auxiliary shifts kept together. -/
theorem auxiliary_invariant_T_grouping (a half k : R) (s : AuxiliaryState R) :
    let s₁ := auxiliaryT a (half * k * s.u ^ 2) s
    let s₂ := auxiliaryT a (-k * s₁.u) s₁
    auxiliaryA a (-half)
        (auxiliaryT a (k * (auxiliaryA a half s₂).u) (auxiliaryA a half s₂)) =
      auxiliaryInvariantT a (half * k) s := by
  dsimp only
  rw [auxiliaryA_conjugates_T_linear_auxiliary_parameter, auxiliaryT_preserves_q,
    auxiliaryT_preserves_q]
  have hu (h : R) (s' : AuxiliaryState R) : (auxiliaryT a h s').u = s'.u := rfl
  simp only [hu, auxiliaryT_comp_parameter_add, auxiliaryInvariantT]
  congr 1
  unfold auxiliaryQ auxiliaryq
  ring

end DimensionFourDependence.Quintic
