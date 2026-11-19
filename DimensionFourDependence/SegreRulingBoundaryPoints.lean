import DimensionFourDependence.SegreFiberCoordinates
import DimensionFourDependence.SinglePoleResidueDirection
import DimensionFourDependence.ValuationProjectiveBoundary

/-! # Single transverse poles give actual points on each Segre ruling -/

namespace DimensionFourDependence

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- The integral normalization at a single transverse pole gives the
specified radial shift as an actual point of the original projective closure. -/
theorem single_pole_radial_shift_projective_boundary {n : ℕ}
    (V : ValuationSubring F) [Algebra E V] [IsScalarTower E V F]
    (x : Fin n → F) (Y Z W c : Fin n → E) (τ v w : F)
    (hx : ∀ i, x i = τ * algebraMap E F (Y i) + v * algebraMap E F (Z i) +
      w * algebraMap E F (W i) + algebraMap E F (c i))
    (hv : 1 < V.valuation v) (hτ : V.valuation τ ≤ V.valuation v) (hw : V.valuation w ≤ 1)
    (hnonzero : ∀ a : IsLocalRing.ResidueField V,
      (fun j : Option (Fin n) => j.elim 0 (fun i => algebraMap E (IsLocalRing.ResidueField V) (Z i) +
        a * algebraMap E (IsLocalRing.ResidueField V) (Y i))) ≠ 0) :
    ∃ a : IsLocalRing.ResidueField V,
      projectiveFieldPoint (E := E)
        (fun j : Option (Fin n) => j.elim 0 (fun i => algebraMap E (IsLocalRing.ResidueField V) (Z i) +
          a * algebraMap E (IsLocalRing.ResidueField V) (Y i))) (hnonzero a) ∈ projectiveClosureSet (L := E) x := by
  let κ := IsLocalRing.ResidueField V
  let π : V →ₐ[E] κ := IsScalarTower.toAlgHom E V κ
  obtain ⟨a, z, hz, hz0, hzi⟩ := single_pole_radial_shift_residue V x Y Z W c τ v w hx hv hτ hw
  have he : (fun j => π (z j)) = fun j : Option (Fin n) => j.elim 0
      (fun i => algebraMap E κ (Z i) + a * algebraMap E κ (Y i)) := by
    funext j
    cases j with
    | none => exact hz0
    | some i => exact hzi i
  have hn : (fun j => π (z j)) ≠ 0 := by rw [he]; exact hnonzero a
  refine ⟨a, ?_⟩
  have hp := residue_field_point_mem_projective_closure π
    (show Function.Injective (algebraMap V F) from Subtype.val_injective) x v⁻¹ z hz hn
  simpa only [he] using hp

variable {κ : Type*} [Field κ] [Algebra E κ]

/-- Every radial shift of the first transverse vector is a nonradial
point of the first ruling, with a fixed transverse coordinate equal to one. -/
theorem segre_first_ruling_shift_identities (Y : Fin 3 → E) (hY0 : Y 0 ≠ 0) (a : κ) :
    let b : Fin 4 → κ := fun i => algebraMap E κ (segreFirstRulingDirection (Y 2 / Y 0) i) +
      a * algebraMap E κ (segreGraphTarget Y i)
    b 2 = algebraMap E κ (Y 2 / Y 0) * b 0 ∧
      b 3 = algebraMap E κ (Y 2 / Y 0) * b 1 ∧
      b 1 - algebraMap E κ (Y 1 / Y 0) * b 0 = 1 := by
  have hr : algebraMap E κ (Y 0) ≠ 0 := (map_ne_zero (algebraMap E κ)).mpr hY0
  dsimp only
  simp [segreFirstRulingDirection, segreGraphTarget, segreGraphFunction, map_div₀, map_mul]
  constructor
  · field_simp
  · constructor <;> field_simp <;> ring

/-- The transposed shift belongs to the second ruling and has its
other transverse coordinate equal to one. -/
theorem segre_second_ruling_shift_identities (Y : Fin 3 → E) (hY0 : Y 0 ≠ 0) (a : κ) :
    let b : Fin 4 → κ := fun i => algebraMap E κ (segreSecondRulingDirection (Y 1 / Y 0) i) +
      a * algebraMap E κ (segreGraphTarget Y i)
    b 1 = algebraMap E κ (Y 1 / Y 0) * b 0 ∧
      b 3 = algebraMap E κ (Y 1 / Y 0) * b 2 ∧
      b 2 - algebraMap E κ (Y 2 / Y 0) * b 0 = 1 := by
  have hr : algebraMap E κ (Y 0) ≠ 0 := (map_ne_zero (algebraMap E κ)).mpr hY0
  dsimp only
  simp [segreSecondRulingDirection, segreGraphTarget, segreGraphFunction, map_div₀, map_mul]
  constructor
  · field_simp
  · constructor <;> field_simp <;> ring

/-- A first transverse pole with the actual single-pole bounds gives
an actual nonradial point at infinity on the first Segre ruling. -/
theorem segre_first_transverse_pole_constructs_boundary_point
    (V : ValuationSubring F) [Algebra E V] [IsScalarTower E V F]
    (Y : Fin 3 → E) (hY0 : Y 0 ≠ 0) (x : Fin 4 → F) (c : E) (τ v w : F)
    (hx : ∀ i, x i = τ * algebraMap E F (segreGraphTarget Y i) +
      v * algebraMap E F (segreFirstRulingDirection (Y 2 / Y 0) i) +
      w * algebraMap E F (segreSecondRulingDirection (Y 1 / Y 0) i) +
      algebraMap E F ((Pi.single 3 c : Fin 4 → E) i))
    (hv : 1 < V.valuation v) (hτ : V.valuation τ ≤ V.valuation v) (hw : V.valuation w ≤ 1) :
    ∃ (a : IsLocalRing.ResidueField V) (b : Fin 4 → IsLocalRing.ResidueField V)
      (hb : (fun j : Option (Fin 4) => j.elim 0 b) ≠ 0),
      (∀ i, b i = algebraMap E (IsLocalRing.ResidueField V) (segreFirstRulingDirection (Y 2 / Y 0) i) +
        a * algebraMap E (IsLocalRing.ResidueField V) (segreGraphTarget Y i)) ∧
      projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 b) hb ∈ projectiveClosureSet (L := E) x ∧
      b 2 = algebraMap E (IsLocalRing.ResidueField V) (Y 2 / Y 0) * b 0 ∧
      b 3 = algebraMap E (IsLocalRing.ResidueField V) (Y 2 / Y 0) * b 1 ∧
      b 1 - algebraMap E (IsLocalRing.ResidueField V) (Y 1 / Y 0) * b 0 = 1 := by
  let b := fun a : IsLocalRing.ResidueField V => fun i =>
    algebraMap E (IsLocalRing.ResidueField V) (segreFirstRulingDirection (Y 2 / Y 0) i) +
      a * algebraMap E (IsLocalRing.ResidueField V) (segreGraphTarget Y i)
  have hn (a : IsLocalRing.ResidueField V) : (fun j : Option (Fin 4) => j.elim 0 (b a)) ≠ 0 := by
    intro he
    have h0 := congrFun he (some 0)
    have h1 := congrFun he (some 1)
    have hk := (segre_first_ruling_shift_identities Y hY0 a).2.2
    change b a 1 - algebraMap E (IsLocalRing.ResidueField V) (Y 1 / Y 0) * b a 0 = 1 at hk
    change b a 0 = 0 at h0
    change b a 1 = 0 at h1
    rw [h0, h1, mul_zero, sub_zero] at hk
    exact zero_ne_one hk
  obtain ⟨a, hp⟩ := single_pole_radial_shift_projective_boundary V x (segreGraphTarget Y)
    (segreFirstRulingDirection (Y 2 / Y 0)) (segreSecondRulingDirection (Y 1 / Y 0))
    (Pi.single 3 c) τ v w hx hv hτ hw hn
  exact ⟨a, b a, hn a, fun _ => rfl, hp, segre_first_ruling_shift_identities Y hY0 a⟩

/-- The second transverse pole constructs the point on the opposite
ruling, with its exact residue shift and nonradial coordinate retained. -/
theorem segre_second_transverse_pole_constructs_boundary_point
    (V : ValuationSubring F) [Algebra E V] [IsScalarTower E V F]
    (Y : Fin 3 → E) (hY0 : Y 0 ≠ 0) (x : Fin 4 → F) (c : E) (τ v w : F)
    (hx : ∀ i, x i = τ * algebraMap E F (segreGraphTarget Y i) +
      v * algebraMap E F (segreFirstRulingDirection (Y 2 / Y 0) i) +
      w * algebraMap E F (segreSecondRulingDirection (Y 1 / Y 0) i) +
      algebraMap E F ((Pi.single 3 c : Fin 4 → E) i))
    (hw : 1 < V.valuation w) (hτ : V.valuation τ ≤ V.valuation w) (hv : V.valuation v ≤ 1) :
    ∃ (a : IsLocalRing.ResidueField V) (b : Fin 4 → IsLocalRing.ResidueField V)
      (hb : (fun j : Option (Fin 4) => j.elim 0 b) ≠ 0),
      (∀ i, b i = algebraMap E (IsLocalRing.ResidueField V) (segreSecondRulingDirection (Y 1 / Y 0) i) +
        a * algebraMap E (IsLocalRing.ResidueField V) (segreGraphTarget Y i)) ∧
      projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 b) hb ∈ projectiveClosureSet (L := E) x ∧
      b 1 = algebraMap E (IsLocalRing.ResidueField V) (Y 1 / Y 0) * b 0 ∧
      b 3 = algebraMap E (IsLocalRing.ResidueField V) (Y 1 / Y 0) * b 2 ∧
      b 2 - algebraMap E (IsLocalRing.ResidueField V) (Y 2 / Y 0) * b 0 = 1 := by
  let b := fun a : IsLocalRing.ResidueField V => fun i =>
    algebraMap E (IsLocalRing.ResidueField V) (segreSecondRulingDirection (Y 1 / Y 0) i) +
      a * algebraMap E (IsLocalRing.ResidueField V) (segreGraphTarget Y i)
  have hn (a : IsLocalRing.ResidueField V) : (fun j : Option (Fin 4) => j.elim 0 (b a)) ≠ 0 := by
    intro he
    have h0 := congrFun he (some 0)
    have h2 := congrFun he (some 2)
    have hk := (segre_second_ruling_shift_identities Y hY0 a).2.2
    change b a 2 - algebraMap E (IsLocalRing.ResidueField V) (Y 2 / Y 0) * b a 0 = 1 at hk
    change b a 0 = 0 at h0
    change b a 2 = 0 at h2
    rw [h0, h2, mul_zero, sub_zero] at hk
    exact zero_ne_one hk
  have hx' (i : Fin 4) : x i = τ * algebraMap E F (segreGraphTarget Y i) +
      w * algebraMap E F (segreSecondRulingDirection (Y 1 / Y 0) i) +
      v * algebraMap E F (segreFirstRulingDirection (Y 2 / Y 0) i) +
      algebraMap E F ((Pi.single 3 c : Fin 4 → E) i) := by rw [hx i]; ring
  obtain ⟨a, hp⟩ := single_pole_radial_shift_projective_boundary V x (segreGraphTarget Y)
    (segreSecondRulingDirection (Y 1 / Y 0)) (segreFirstRulingDirection (Y 2 / Y 0))
    (Pi.single 3 c) τ w v hx' hw hτ hv hn
  exact ⟨a, b a, hn a, fun _ => rfl, hp, segre_second_ruling_shift_identities Y hY0 a⟩

end DimensionFourDependence
