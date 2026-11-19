import DimensionFourDependence.TernaryParameterSlopeFrame
import DimensionFourDependence.TernaryParameterCubicObstruction
import DimensionFourDependence.TernaryParameterTransverseConstants

/-! # The middle output is affine with coefficients in the closed parameter field -/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u
set_option maxHeartbeats 3700000

variable {K : Type u} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "F" => FractionRing R₃
local notation "ι" => (algebraMap R₃ F)
local notation "D₀" => (rationalPartial (K := K) (n := 3))
local notation "x₀" => (rationalCoordinate (K := K) (n := 3))

/-- The normalized nilpotent trace and minor, along with the nonconstant
slope, force the actual middle output to be affine in the two outer
source coordinates over the relative closed parameter field. -/
theorem ternary_parameter_middle_output_affine_over_parameter_field
    (r : R₃) (v U V α : F) (hU : U ≠ 0) (hα : α ≠ 0)
    (hr : D₀ 1 (ι r) ≠ 0)
    (hR : algebraicClosure (IntermediateField.adjoin K {ι r}) F = ⊥)
    (hUα : ∀ E : Derivation K F F, E (ι r) = 0 → E U = 0 ∧ E α = 0)
    (ha : ∀ E : Derivation K F F, E (V / U) = α * E (ι r))
    (ht : U * D₀ 0 (ι r) + V * D₀ 2 (ι r) + D₀ 1 v = 0)
    (hm : (U * D₀ 0 (ι r) + V * D₀ 2 (ι r)) * D₀ 1 v -
      D₀ 1 (ι r) * (U * D₀ 0 v + V * D₀ 2 v) = 0) :
    let L := IntermediateField.adjoin K {ι r}
    ∃ a b c : L, v = (a : F) * x₀ 2 + (b : F) * x₀ 0 + (c : F) := by
  let x := x₀ 0
  let y := x₀ 1
  let z := x₀ 2
  let a := V / U
  let s := z - a * x
  let ρ := ι r
  let Y : Fin 3 → F := ![x, ρ, s]
  have hY : AlgebraicIndependent K Y :=
    ternary_parameter_transverse_frame_independent ρ a α hr (fun i => ha (D₀ i))
  have htr : Algebra.trdeg K F ≤ 3 := by rw [rationalSource_trdeg_eq]; norm_num
  have hB := hY.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by simpa using htr)
  let D := fullBasisPartial Y hB 0
  let E := fullBasisPartial Y hB 1
  let G := fullBasisPartial Y hB 2
  have hD (i : Fin 3) : D (Y i) = if i = 0 then 1 else 0 := fullBasisPartial_coordinate Y hB 0 i
  have hE (i : Fin 3) : E (Y i) = if i = 1 then 1 else 0 := fullBasisPartial_coordinate Y hB 1 i
  have hG (i : Fin 3) : G (Y i) = if i = 2 then 1 else 0 := fullBasisPartial_coordinate Y hB 2 i
  have hDx : D x = 1 := hD 0
  have hDρ : D ρ = 0 := hD 1
  have hDs : D s = 0 := hD 2
  have hEx : E x = 0 := hE 0
  have hGx : G x = 0 := hG 0
  have hGs : G s = 1 := hG 2
  have hDE (w : F) : D (E w) = E (D w) := fullBasisPartials_commute Y hB 0 1 w
  have hDG (w : F) : D (G w) = G (D w) := fullBasisPartials_commute Y hB 0 2 w
  let c := D₀ 1 v / (U * D₀ 1 ρ)
  let Δ := D₀ 0 + c • D₀ 1 + a • D₀ 2
  obtain ⟨hΔr, hΔv, hΔx, hΔy, hΔz⟩ := ternary_parameter_normalized_derivation_tangent ρ v U V hU hr ht hm
  change Δ ρ = 0 at hΔr
  change Δ v = 0 at hΔv
  change Δ x = 1 at hΔx
  change Δ y = c at hΔy
  change Δ z = a at hΔz
  have hDΔ : D = Δ := by
    apply fullBasis_derivation_ext Y hB
    intro i
    fin_cases i
    · exact hDx.trans hΔx.symm
    · exact hDρ.trans hΔr.symm
    · change D s = Δ s
      have hΔa : Δ a = 0 := by rw [show Δ a = α * Δ ρ from ha Δ, hΔr, mul_zero]
      rw [hDs]
      change 0 = Δ (z - a * x)
      simp only [map_sub, Δ.leibniz, smul_eq_mul, hΔx, hΔz, hΔa,
        mul_one, mul_zero, add_zero, sub_self]
  have hDv : D v = 0 := by rw [hDΔ, hΔv]
  have hOuter : D₀ 1 = (D₀ 1 ρ) • (E - (α * x) • G) := by
    apply fullBasis_derivation_ext Y hB
    have hx1 : D₀ 1 x = 0 := rationalPartial_coordinate 1 0
    have hz1 : D₀ 1 z = 0 := rationalPartial_coordinate 1 2
    intro i
    simp only [Derivation.smul_apply, Derivation.sub_apply, smul_eq_mul, hE, hG]
    fin_cases i
    · change D₀ 1 x = _
      simp [hx1]
    · change D₀ 1 ρ = _
      simp
    · change D₀ 1 (z - a * x) = _
      simp [Derivation.leibniz, smul_eq_mul, hz1, hx1, show D₀ 1 a = α * D₀ 1 ρ from ha _]
      ring
  have hChain (w : F) : D₀ 1 w = D₀ 1 ρ * (E w - α * x * G w) := by
    have he := DFunLike.congr_fun hOuter w
    simpa only [Derivation.smul_apply, Derivation.sub_apply, smul_eq_mul, mul_assoc] using he
  have hOne : ι (pderiv 1 r) * (E y - α * x * G y) = 1 := by
    rw [← rationalPartial_polynomial, ← hChain]
    exact rationalPartial_coordinate 1 1
  obtain ⟨hDU, hDα⟩ := hUα D hDρ
  let m := E v / U
  let n := -(α * G v) / (2 * U)
  have hDm : D m = 0 := by simp [m, D.leibniz_div, hDE, hDv, hDU, smul_eq_mul]
  have hDn : D n = 0 := by
    simp [n, D.leibniz_div, D.leibniz, hDG, hDv, hDU, hDα, smul_eq_mul, show D 2 = 0 from D.map_natCast 2]
  have hDy : D y = m + 2 * n * x := by
    rw [hDΔ, hΔy]
    change D₀ 1 v / (U * D₀ 1 ρ) = _
    rw [hChain]
    dsimp [m, n]
    field_simp [hU, show D₀ 1 ρ ≠ 0 from hr]
    ring
  obtain ⟨k, hDk, hy⟩ := derivation_slice_integrates_affine_value D x y m n hDx hDm hDn hDy
  have hDa : D a = 0 := by rw [show D a = α * D ρ from ha D, hDρ, mul_zero]
  have hCub := ternary_parameter_slice_cubic_coefficient_zero D E G r a s α k m n
    hDx hEx hGx hDE hDG hDa hDs hDα hDk hDm hDn hy (by dsimp [s]; ring) hOne
  have hGn : G n = 0 := (mul_eq_zero.mp hCub).resolve_left hα
  obtain ⟨hGU, hGα⟩ := hUα G (hG 1)
  have hSecond : G (G v) = 0 := by
    have he : G n = -(α * G (G v)) / (2 * U) := by
      dsimp [n]
      rw [G.leibniz_div]
      simp only [G.leibniz, map_neg, smul_eq_mul, show G 2 = 0 from G.map_natCast 2, hGU, hGα,
        mul_zero, add_zero, sub_zero]
      field_simp
    rw [he, div_eq_zero_iff, neg_eq_zero, mul_eq_zero] at hGn
    rcases hGn with (h | h) | h
    · exact (hα h).elim
    · exact h
    · exact (mul_ne_zero two_ne_zero hU h).elim
  let L := IntermediateField.adjoin K {ρ}
  have hMem (w : F) (hwD : D w = 0) (hwG : G w = 0) : w ∈ L :=
    ternary_parameter_joint_constants_mem_closed_parameter_field x ρ s hB htr hR w hwD hwG
  have hgv : G v ∈ L := hMem (G v) (by rw [hDG, hDv, map_zero]) hSecond
  have hv0 : v - s * G v ∈ L := by
    apply hMem
    · rw [map_sub, D.leibniz, hDG, hDv, map_zero, hDs]
      simp
    · rw [map_sub, G.leibniz, hSecond, hGs]
      simp [smul_eq_mul]
  have hal : a ∈ L := hMem a hDa (by rw [show G a = α * G ρ from ha G, show G ρ = 0 from hG 1, mul_zero])
  refine ⟨⟨G v, hgv⟩, ⟨-a * G v, mul_mem (neg_mem hal) hgv⟩, ⟨v - s * G v, hv0⟩, ?_⟩
  change v = G v * z + (-a * G v) * x + (v - s * G v)
  dsimp [s]
  ring

end DimensionFourDependence
