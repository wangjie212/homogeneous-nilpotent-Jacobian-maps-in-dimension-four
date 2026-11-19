import DimensionFourDependence.QuinticSecondFlowTameness
import DimensionFourDependence.QuinticStateSubstitution

/-! # The actual tame word for the shifted parameter in (6.40) -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "x" => (X 0 : R₄)
local notation "y" => (X 1 : R₄)
local notation "z" => (X 2 : R₄)
local notation "t" => (X 3 : R₄)
local notation "half" => (C (2 : K)⁻¹ : R₄)
local notation "s" => (ActiveState.mk x y z)

private theorem state_and_fixed_coordinate_of_images (E : Aut₄) (w : ActiveState R₄)
    (hX : ∀ j : Fin 4, E (X j) = ![w.x, w.y, w.z, t] j) :
    (s).map E.toRingHom = w ∧ E t = t := by
  have hx : E x = w.x := hX 0
  have hy : E y = w.y := hX 1
  have hz : E z = w.z := hX 2
  refine ⟨?_, hX 3⟩
  change ActiveState.mk (E x) (E y) (E z) = w
  rw [hx, hy, hz]

private theorem substitute_second_flow (E : Aut₄) (hEt : E t = t) (k : R₄) :
    (secondLiftFlow half t k s).map E.toRingHom =
      secondLiftFlow half t (E k) ((s).map E.toRingHom) := by
  have he : E.toRingHom half = half := E.commutes _
  have ht : E.toRingHom t = t := hEt
  rw [map_secondLiftFlow, he, ht]
  rfl

private theorem substitute_parameter_shift (E : Aut₄) (hEt : E t = t) (c : K) :
    (parameterShift t (C c * secondInvariant half t s) s).map E.toRingHom =
      parameterShift t (C c * secondInvariant half t ((s).map E.toRingHom)) ((s).map E.toRingHom) := by
  have he : E.toRingHom half = half := E.commutes _
  have hc : E.toRingHom (C c : R₄) = C c := E.commutes _
  have ht : E.toRingHom t = t := hEt
  rw [map_parameterShift, map_mul, map_secondInvariant, he, ht, hc]

/-- The checked word with the parameter of (6.40), allowing any added
polynomial g(y,t) and any coefficient of ty in the shifting parameter. -/
theorem quintic_shifted_second_flow_is_tame (c : K) (g : R₂) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧ E t = t ∧
      (s).map E.toRingHom =
        secondLiftFlow half t
          (C c * t ^ 2 * secondInvariant half t s + coefficientPlane g) s := by
  let h : R₂ := C c * X 1 * X 0
  let d : R₄ := C c * t
  let q := secondInvariant half t s
  let v := coefficientPlane g
  let w₀ := secondLiftFlow half t v s
  let w₁ := secondLiftFlow half t (-(d * w₀.y)) w₀
  let w₂ := parameterShift t q w₁
  let w₃ := secondLiftFlow half t (d * w₂.y) w₂
  let w₄ := parameterShift t (-q) w₃
  have hhalf : 2 * half = 1 := original_quintic_half_identity
  have hh : coefficientPlane h = d * y := by
    simp [h, d, coefficientPlane, algebraMap_eq]
  have hneg : coefficientPlane (-h) = -(d * y) := by rw [map_neg, hh]
  obtain ⟨G, hGt, hGX⟩ := quintic_second_flow_is_tame g
  obtain ⟨M, hMt, hMX⟩ := quintic_second_flow_is_tame (-h)
  obtain ⟨P, hPt, hPX⟩ := quintic_parameter_shift_is_tame (1 : K)
  obtain ⟨V, hVt, hVX⟩ := quintic_second_flow_is_tame h
  obtain ⟨N, hNt, hNX⟩ := quintic_parameter_shift_is_tame (-1 : K)
  obtain ⟨hG, hGfix⟩ := state_and_fixed_coordinate_of_images G w₀ hGX
  obtain ⟨hM, hMfix⟩ := state_and_fixed_coordinate_of_images M
    (secondLiftFlow half t (coefficientPlane (-h)) s) hMX
  obtain ⟨hP, hPfix⟩ := state_and_fixed_coordinate_of_images P
    (parameterShift t (C (1 : K) * q) s) hPX
  obtain ⟨hV, hVfix⟩ := state_and_fixed_coordinate_of_images V
    (secondLiftFlow half t (coefficientPlane h) s) hVX
  obtain ⟨hN, hNfix⟩ := state_and_fixed_coordinate_of_images N
    (parameterShift t (C (-1 : K) * q) s) hNX
  have hmapd (F : Aut₄) (ht : F t = t) : F d = d := by
    have hc : F (C c) = C c := F.commutes c
    simp only [d, map_mul, ht, hc]
  have hmapy (F : Aut₄) (w : ActiveState R₄) (hw : (s).map F.toRingHom = w) : F y = w.y :=
    congrArg ActiveState.y hw
  let E₁ := G * M
  let E₂ := E₁ * P
  let E₃ := E₂ * V
  let E₄ := E₃ * N
  have h₁t : E₁ t = t := by change G (M t) = t; rw [hMfix, hGfix]
  have h₂t : E₂ t = t := by change E₁ (P t) = t; rw [hPfix, h₁t]
  have h₃t : E₃ t = t := by change E₂ (V t) = t; rw [hVfix, h₂t]
  have h₄t : E₄ t = t := by change E₃ (N t) = t; rw [hNfix, h₃t]
  have hq₀ : secondInvariant half t w₀ = q :=
    secondLiftFlow_preserves_invariant half t v s hhalf
  have hq₁ : secondInvariant half t w₁ = q :=
    (secondLiftFlow_preserves_invariant _ _ _ _ hhalf).trans hq₀
  have hq₂ : secondInvariant half t w₂ = q :=
    (parameterShift_preserves_invariant _ _ _ _).trans hq₁
  have hq₃ : secondInvariant half t w₃ = q :=
    (secondLiftFlow_preserves_invariant _ _ _ _ hhalf).trans hq₂
  have h₁ : (s).map E₁.toRingHom = w₁ := by
    change ((s).map M.toRingHom).map G.toRingHom = _
    rw [hM, substitute_second_flow G hGfix, hneg, map_neg, map_mul, hmapd G hGfix,
      hmapy G w₀ hG, hG]
  have h₂ : (s).map E₂.toRingHom = w₂ := by
    change ((s).map P.toRingHom).map E₁.toRingHom = _
    rw [hP, substitute_parameter_shift E₁ h₁t, h₁, hq₁, map_one, one_mul]
  have h₃ : (s).map E₃.toRingHom = w₃ := by
    change ((s).map V.toRingHom).map E₂.toRingHom = _
    rw [hV, substitute_second_flow E₂ h₂t, hh, map_mul, hmapd E₂ h₂t,
      hmapy E₂ w₂ h₂, h₂]
  have h₄ : (s).map E₄.toRingHom = w₄ := by
    change ((s).map N.toRingHom).map E₃.toRingHom = _
    rw [hN, substitute_parameter_shift E₃ h₃t, h₃, hq₃, map_neg, map_one, neg_one_mul]
  have hw := secondLiftFlow_parameter_shifting_commutator half t d w₀ hhalf
  dsimp only at hw
  rw [hq₀] at hw
  change w₄ = secondLiftFlow half t (d * t * q) w₀ at hw
  have hword : E₄ ∈ Tame.subgroup K 4 := (Tame.subgroup K 4).mul_mem
    ((Tame.subgroup K 4).mul_mem
      ((Tame.subgroup K 4).mul_mem ((Tame.subgroup K 4).mul_mem hGt hMt) hPt) hVt) hNt
  refine ⟨E₄, hword, h₄t, ?_⟩
  rw [h₄, hw]
  change secondLiftFlow half t (d * t * q) (secondLiftFlow half t v s) =
    secondLiftFlow half t (C c * t ^ 2 * q + v) s
  rw [secondLiftFlow_add _ _ _ _ _ hhalf]
  congr 1
  dsimp only [d]
  ring

end DimensionFourDependence.Quintic
