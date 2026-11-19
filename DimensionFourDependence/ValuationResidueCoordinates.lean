import DimensionFourDependence.CubicRadialShift

/-! # Integral homogeneous coordinates at a valuation pole

The largest source-coordinate value gives a common normalization. The
homogenizing coordinate reduces to zero and one affine coordinate reduces
to one, producing a genuine nonzero direction at infinity.
-/

namespace DimensionFourDependence

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- Constants contained in a valuation subring define its coefficient algebra. -/
@[instance_reducible]
noncomputable def valuationConstantAlgebra (V : ValuationSubring F)
    (hV : ∀ c : E, algebraMap E F c ∈ V) : Algebra E V := by
  let f : E →+* V :=
    { toFun := fun c => ⟨algebraMap E F c, hV c⟩
      map_one' := Subtype.ext (map_one (algebraMap E F))
      map_mul' := fun a b => Subtype.ext (map_mul (algebraMap E F) a b)
      map_zero' := Subtype.ext (map_zero (algebraMap E F))
      map_add' := fun a b => Subtype.ext (map_add (algebraMap E F) a b) }
  exact f.toAlgebra

theorem valuationConstantScalarTower (V : ValuationSubring F)
    (hV : ∀ c : E, algebraMap E F c ∈ V) :
    let := valuationConstantAlgebra V hV
    IsScalarTower E V F := by
  let := valuationConstantAlgebra V hV
  exact IsScalarTower.of_algebraMap_eq (by intro c; rfl)

omit [Field E] [Algebra E F] in
/-- Vanishing in the residue field is the strict valuation bound. -/
theorem valuation_residue_zero_iff (V : ValuationSubring F) (a : V) :
    IsLocalRing.residue V a = 0 ↔ V.valuation (a : F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, V.valuation_lt_one_iff]

omit [Field E] [Algebra E F] in
/-- Normalize a tuple by a coordinate of largest value that has a pole. -/
theorem valuation_normalized_infinity_coordinates {n : ℕ}
    (V : ValuationSubring F) (x : Fin n → F) (k : Fin n)
    (hk : 1 < V.valuation (x k)) (hmax : ∀ i, V.valuation (x i) ≤ V.valuation (x k)) :
    ∃ (s : F) (z : Option (Fin n) → V),
      (z none : F) = s ∧ (∀ i, (z (some i) : F) = s * x i) ∧
      IsLocalRing.residue V (z none) = 0 ∧ IsLocalRing.residue V (z (some k)) = 1 := by
  classical
  have hk0 : x k ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hk
    exact (not_lt_of_ge zero_le_one) hk
  have hknot : x k ∉ V := fun h => (not_le_of_gt hk) ((V.valuation_le_one_iff _).mpr h)
  have hinv : (x k)⁻¹ ∈ V := (V.mem_or_inv_mem (x k)).resolve_left hknot
  let b : V := ⟨(x k)⁻¹, hinv⟩
  have hb : IsLocalRing.residue V b = 0 := by
    apply (valuation_residue_zero_iff V b).mpr
    change V.valuation ((x k)⁻¹) < 1
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hk
  choose a ha using fun i => (V.valuation_le_iff (x i) (x k)).mp (hmax i)
  have hak : a k = 1 := by
    apply Subtype.ext
    apply mul_right_cancel₀ hk0
    simpa only [OneMemClass.coe_one, one_mul] using ha k
  let z : Option (Fin n) → V := fun j => j.elim b a
  refine ⟨(x k)⁻¹, z, rfl, ?_, hb, ?_⟩
  · intro i
    change (a i : F) = (x k)⁻¹ * x i
    have he := (eq_div_iff hk0).mpr (ha i)
    simpa only [div_eq_mul_inv, mul_comm] using he
  · change IsLocalRing.residue V (a k) = 1
    rw [hak, map_one]

omit [Field E] [Algebra E F] in
/-- Any coordinate pole gives a nonzero normalized residue direction at infinity. -/
theorem exists_valuation_infinity_coordinates {n : ℕ}
    (V : ValuationSubring F) (x : Fin n → F) (i : Fin n) (hi : 1 < V.valuation (x i)) :
    ∃ (k : Fin n) (s : F) (z : Option (Fin n) → V),
      (z none : F) = s ∧ (∀ j, (z (some j) : F) = s * x j) ∧
      IsLocalRing.residue V (z none) = 0 ∧ IsLocalRing.residue V (z (some k)) = 1 := by
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (fun j => V.valuation (x j))
    ⟨i, Finset.mem_univ i⟩
  obtain ⟨s, z, hz⟩ := valuation_normalized_infinity_coordinates V x k
    (hi.trans_le (hk i (Finset.mem_univ i))) (fun j => hk j (Finset.mem_univ j))
  exact ⟨k, s, z, hz⟩

end DimensionFourDependence
