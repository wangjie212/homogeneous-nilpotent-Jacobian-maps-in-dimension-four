import DimensionFourDependence.QuinticBasicLiftTameness

/-! # The tame lift with parameter in K[u,t], equation (6.25) -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

set_option maxHeartbeats 1500000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "x" => (X 0 : R₄)
local notation "y" => (X 1 : R₄)
local notation "z" => (X 2 : R₄)
local notation "t" => (X 3 : R₄)
local notation "half" => (C (2 : K)⁻¹ : R₄)
local notation "b" => (quinticAuxiliaryState half x y z t)

/-- Each auxiliary-only parameter has a checked polynomial tame lift
in the original variables. -/
theorem quintic_auxiliary_only_flow_is_tame (η : K) (g : R₂) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧ E t = t ∧
      let h := t ^ 2 * aeval ![(b).u, t] g
      (b).map E.toRingHom = auxiliaryT (C η * t) h b := by
  let u₃ : R₃ := C (2 : K)⁻¹ * (X 0 + X 2)
  let v₃ : R₃ := C (2 : K)⁻¹ * (X 0 - X 2)
  let D : R₂ →ₐ[K] R₃ := aeval ![u₃, X 1]
  let F : R₃ := 2 * v₃ * D g - C η * X 1 ^ 3 * (D g) ^ 2
  let U := coordinateU x y z t
  let E : R₃ →ₐ[K] R₄ := aeval ![U, t, z]
  let G := aeval (![(b).u, t] : Fin 2 → R₄) g
  let h := t ^ 2 * G
  let κ := 2 * (b).v * G - C η * t ^ 3 * G ^ 2
  let a := C η * t
  have hC (d : K) : E (C d) = C d := E.commutes _
  have e₀ : E (X 0) = U := aeval_X _ _
  have e₁ : E (X 1) = t := aeval_X _ _
  have e₂ : E (X 2) = z := aeval_X _ _
  have eu : E u₃ = (b).u := by
    simp only [u₃, map_mul, map_add, hC, e₀, e₂]
    rfl
  have ev : E v₃ = (b).v := by
    simp only [v₃, map_mul, map_sub, hC, e₀, e₂]
    rfl
  have eD : E.comp D = aeval ![(b).u, t] := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, D, aeval_X]
    fin_cases j
    · exact eu
    · exact e₁
  have eg : E (D g) = G := AlgHom.congr_fun eD g
  have eF : E F = κ := by
    simp only [F, κ, map_mul, map_sub, map_pow, map_ofNat, ev, eg, hC, e₁]
  obtain ⟨P, hP, hPt, hPs⟩ := quintic_auxiliary_p_shift_is_tame F
  change (b).map P.toRingHom = auxiliaryPShift (t ^ 2 * E F) b at hPs
  rw [eF] at hPs
  obtain ⟨V, hV, hVt, hVs⟩ := quintic_auxiliary_v_shift_is_tame η g
  change (b).map V.toRingHom = auxiliaryVShift (a * h) b at hVs
  have hu : V (b).u = (b).u := congrArg AuxiliaryState.u hVs
  have hvg : V G = G := by
    change V.toAlgHom (aeval ![(b).u, t] g) = _
    rw [Tame.algHom_aeval]
    have hv : (fun j : Fin 2 => V.toAlgHom (![(b).u, t] j)) = ![(b).u, t] := by
      funext j
      fin_cases j
      · exact hu
      · exact hVt
    rw [hv]
  let w := auxiliaryVShift (a * h) b
  have hv : V (b).v = w.v := congrArg AuxiliaryState.v hVs
  have hη : V (C η) = C η := V.commutes _
  have hvκ : V κ = 2 * w.v * G - C η * t ^ 3 * G ^ 2 := by
    simp only [κ, map_mul, map_sub, map_pow, map_ofNat, hv, hvg, hVt, hη]
  let A := V * P
  refine ⟨A, (Tame.subgroup K 4).mul_mem hV hP, ?_, ?_⟩
  · change V (P t) = t
    rw [hPt, hVt]
  · change ((b).map P.toRingHom).map V.toRingHom = auxiliaryT a h b
    rw [hPs, auxiliaryT_eq_auxiliary_shifts]
    change (auxiliaryPShift (t ^ 2 * κ) b).map V.toRingHom =
      auxiliaryPShift (2 * w.v * h - a * h ^ 2) w
    have hp : (auxiliaryPShift (t ^ 2 * κ) b).map V.toRingHom =
        auxiliaryPShift (V (t ^ 2 * κ)) ((b).map V.toRingHom) := by
      simp only [auxiliaryPShift, AuxiliaryState.map, map_add]
      rfl
    rw [hp, hVs]
    have he : V (t ^ 2 * κ) = 2 * w.v * h - a * h ^ 2 := by
      rw [map_mul, map_pow, hVt, hvκ]
      dsimp only [h, a]
      ring
    rw [he]

end DimensionFourDependence.Quintic
