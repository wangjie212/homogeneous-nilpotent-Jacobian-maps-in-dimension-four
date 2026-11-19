import DimensionFourDependence.QuinticTriangularFrameShear
import DimensionFourDependence.QuinticGroupedAuxiliaryFactors
import DimensionFourDependence.QuinticSecondLiftTameShears

/-! # The actual tame lift of the first grouped conjugate, (6.31) -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1600000

private theorem grouped_first_coordinate_result {R : Type*} [CommRing R]
    (half η scale t : R) (b : AuxiliaryState R) :
    let r := b.u + half * auxiliaryq (η * t) b
    let f := 2 * scale * b.v * r - η * scale ^ 2 * t ^ 3 * r ^ 2
    AuxiliaryState.mk (b.p + t ^ 2 * f) b.v (b.u - half * η * t ^ 3 * f) =
      groupedAuxiliaryFirst (η * t) half (scale * t ^ 2) b := by
  let r := b.u + half * auxiliaryq (η * t) b
  let f := 2 * scale * b.v * r - η * scale ^ 2 * t ^ 3 * r ^ 2
  change AuxiliaryState.mk (b.p + t ^ 2 * f) b.v (b.u - half * η * t ^ 3 * f) = _
  rw [groupedAuxiliaryFirst_coordinates (η * t) half (scale * t ^ 2) b]
  change _ = AuxiliaryState.mk
    (b.p + (2 * b.v * (scale * t ^ 2 * r) - η * t * (scale * t ^ 2 * r) ^ 2))
    b.v (b.u - half * (η * t) * (2 * b.v * (scale * t ^ 2 * r) - η * t * (scale * t ^ 2 * r) ^ 2))
  have h : 2 * b.v * (scale * t ^ 2 * r) - η * t * (scale * t ^ 2 * r) ^ 2 = t ^ 2 * f := by
    dsimp only [f]
    ring
  rw [h]
  congr 1
  ring

variable {K : Type*} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "x" => (X 0 : R₄)
local notation "y" => (X 1 : R₄)
local notation "z" => (X 2 : R₄)
local notation "t" => (X 3 : R₄)
local notation "half" => (C (2 : K)⁻¹ : R₄)
local notation "s" => (ActiveState.mk x y z)
local notation "b" => (quinticAuxiliaryState half x y z t)

theorem quintic_grouped_first_is_tame (η scale : K) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧ E t = t ∧
      (b).map E.toRingHom = groupedAuxiliaryFirst (C η * t) half (C scale * t ^ 2) b := by
  let w := firstLiftFrame half (C η) t s
  let v₃ : R₃ := C (2 : K)⁻¹ * (X 0 - X 2)
  let r₃ : R₃ := X 2 + v₃ - C (2 : K)⁻¹ * v₃ ^ 2
  let p₃ : R₃ := 2 * C scale * v₃ * r₃ - C (η * scale ^ 2) * X 1 ^ 3 * r₃ ^ 2
  let r := (b).u + half * auxiliaryq (C η * t) b
  let f := 2 * C scale * (b).v * r - C η * (C scale) ^ 2 * t ^ 3 * r ^ 2
  let ev : R₃ →ₐ[K] R₄ := aeval ![coordinateU w.x w.y w.z t, t, w.z]
  have hh : 2 * half = 1 := original_quintic_half_identity
  have hC (d : K) : ev (C d) = C d := ev.commutes d
  have he₀ : ev (X 0) = coordinateU w.x w.y w.z t := aeval_X _ _
  have he₁ : ev (X 1) = t := aeval_X _ _
  have he₂ : ev (X 2) = w.z := aeval_X _ _
  have he_v : ev v₃ = (b).v := by
    simp only [v₃, map_mul, map_sub, hC, he₀, he₂]
    exact (firstLiftFrame_v_parameter half (C η) t s).symm
  have he_r : ev r₃ = r := by
    simp only [r₃, map_add, map_sub, map_mul, map_pow, hC, he₂, he_v]
    exact (firstLiftFrame_r_parameter half (C η) t s hh).symm
  have he_f : ev p₃ = f := by
    simp only [p₃, f, map_mul, map_sub, map_pow, map_ofNat, hC, he₁, he_v, he_r]
  obtain ⟨A, hA, hAX⟩ := quintic_first_lift_frame_is_tame η
  obtain ⟨E, hE, hEX⟩ := tame_xy_invariant_shear_in_frame A hA p₃
  have hAx : A x = w.x := hAX 0
  have hAy : A y = w.y := hAX 1
  have hAz : A z = w.z := hAX 2
  have hAt : A t = t := hAX 3
  dsimp only at hEX
  rw [hAx, hAy, hAz, hAt, show aeval ![coordinateU w.x w.y w.z t, t, w.z] p₃ = f from he_f] at hEX
  have hEt : E t = t := hEX.2.2.2
  have hwm : w.map E.toRingHom = parameterShift t f w := by
    change ActiveState.mk (E w.x) (E w.y) (E w.z) =
      ⟨w.x - w.z * f, w.y + t * f, w.z⟩
    rw [hEX.1, hEX.2.1, hEX.2.2.1]
  have hEhalf : E.toRingHom half = half := E.commutes _
  have hEeta : E.toRingHom (C η : R₄) = C η := E.commutes _
  have hEt' : E.toRingHom t = t := hEt
  have hw' : w.map E.toRingHom = firstLiftFrame half (C η) t ((s).map E.toRingHom) := by
    simp only [w, ActiveState.map, firstLiftFrame, map_add, map_sub, map_mul, map_pow,
      hEt', hEhalf, hEeta]
  have hs : (s).map E.toRingHom = firstLiftFrameInv half (C η) t (parameterShift t f w) := by
    have he := congrArg (firstLiftFrameInv half (C η) t) (hw'.symm.trans hwm)
    rwa [firstLiftFrameInv_frame] at he
  refine ⟨E, hE, hEt, ?_⟩
  have haux := map_quinticAuxiliaryState E.toRingHom half t s
  rw [hEhalf, hEt'] at haux
  have ha := quintic_first_lift_auxiliary_coordinates half (C η) t f s hh
  dsimp only at ha
  change (b).map E.toRingHom =
    groupedAuxiliaryFirst (C η * t) half (C scale * t ^ 2) b
  calc
    (b).map E.toRingHom = ⟨(b).p + t ^ 2 * f, (b).v, (b).u - half * C η * t ^ 3 * f⟩ := by
      rw [haux]
      change quinticAuxiliaryState half ((s).map E.toRingHom).x ((s).map E.toRingHom).y
        ((s).map E.toRingHom).z t = _
      rw [hs]
      exact ha
    _ = _ := grouped_first_coordinate_result half (C η) (C scale) t b

end DimensionFourDependence.Quintic
