import DimensionFourDependence.NativeRationalRootTransfer

/-! # Full rational cone-coordinate formulas transfer with homogeneous relations

Clearing the specified rational root denominator makes all four formulas
homogeneous polynomial identities of degree d(d+1). Equality of the actual
homogeneous vanishing ideals transfers the denominator, root nonvanishing,
and complete cone formula, including its last coordinate.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {E F G : Type*} [Field E] [Field F] [Field G] [Algebra E F] [Algebra E G]

/-- The full last cone formula is equivalent to its degree-d(d+1)
cleared identity at every nonzero rational root denominator. -/
theorem rational_cone_last_coordinate_iff_cleared
    {L : Type*} [Field L] (y a b u m l : L) {d : ℕ} (hd : 0 < d) (hm : m ≠ 0) :
    y = a * (u / m) ^ d + b * (u / m) ^ (d - 1) * l ↔
      y * m ^ d = a * u ^ d + b * u ^ (d - 1) * l * m := by
  have hp : m ^ (d - 1) * m = m ^ d := by rw [← pow_succ]; congr 1; omega
  have hfirst : (u / m) ^ d * m ^ d = u ^ d := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero d hm)]
  have hlast : (u / m) ^ (d - 1) * l * m ^ d = u ^ (d - 1) * l * m := by
    rw [div_pow, ← hp]
    field_simp [hm]
  have hclear : (a * (u / m) ^ d + b * (u / m) ^ (d - 1) * l) * m ^ d =
      a * u ^ d + b * u ^ (d - 1) * l * m := by
    calc
      _ = a * ((u / m) ^ d * m ^ d) + b * ((u / m) ^ (d - 1) * l * m ^ d) := by ring
      _ = _ := by rw [hfirst, hlast]; ring
  constructor
  · intro he
    rw [he]
    exact hclear
  · intro he
    exact mul_right_cancel₀ (pow_ne_zero d hm) (he.trans hclear.symm)

/-- The last cone-coordinate formula has a homogeneous cleared
polynomial of the same degree as the three transverse formulas. -/
theorem rational_cone_last_cleared_polynomial_homogeneous
    (Y N M L : MvPolynomial (Fin 4) E) {d : ℕ} (hd : 0 < d)
    (hY : Y.IsHomogeneous d) (hN : N.IsHomogeneous d) (hM : M.IsHomogeneous d)
    (hL : L.IsHomogeneous 1) (a b : E) :
    (Y * M ^ d - (C a * (N * L) ^ d + C b * (N * L) ^ (d - 1) * L * M)).IsHomogeneous
      (d * (d + 1)) := by
  have hleft : (Y * M ^ d).IsHomogeneous (d * (d + 1)) := by
    convert hY.mul (hM.pow d) using 1; ring
  have hfirst : (C a * (N * L) ^ d).IsHomogeneous (d * (d + 1)) := by
    convert ((hN.mul hL).pow d).C_mul a using 1; ring
  have hlast : (C b * (N * L) ^ (d - 1) * L * M).IsHomogeneous (d * (d + 1)) := by
    have he : (d + 1) * (d - 1) + 1 + d = d * (d + 1) := by
      calc
        _ = (d + 1) * ((d - 1) + 1) := by ring
        _ = _ := by rw [Nat.sub_add_cancel hd]; ring
    convert ((((hN.mul hL).pow (d - 1)).C_mul b).mul hL).mul hM using 1
    exact he.symm
  exact hleft.sub (hfirst.add hlast)

/-- Two actual source points with identical homogeneous relations
retain the nonzero denominator, nonzero rational root and all four
cone-coordinate formulas. No map between their full fields is assumed. -/
theorem homogeneous_relations_transfer_full_rational_cone_form
    (Y : Fin 4 → MvPolynomial (Fin 4) E) {d : ℕ} (hd : 0 < d)
    (hY : ∀ i, (Y i).IsHomogeneous d)
    (N M L : MvPolynomial (Fin 4) E) (hN : N.IsHomogeneous d) (hM : M.IsHomogeneous d)
    (hL : L.IsHomogeneous 1) (x : Fin 4 → F) (z : Fin 4 → G)
    (hrel : ∀ (P : MvPolynomial (Fin 4) E) (n : ℕ), P.IsHomogeneous n →
      (aeval x P = 0 ↔ aeval z P = 0))
    (r : F) (hr : r ≠ 0) (hm : aeval x M ≠ 0)
    (hroot : r = aeval x N * aeval x L / aeval x M)
    (V : Fin 3 → E) (a b : E)
    (hfirst : ∀ i : Fin 3, aeval x (Y i.castSucc) = algebraMap E F (V i) * r ^ d)
    (hlast : aeval x (Y (Fin.last 3)) = algebraMap E F a * r ^ d +
      algebraMap E F b * r ^ (d - 1) * aeval x L) :
    aeval z M ≠ 0 ∧
      let R := aeval z N * aeval z L / aeval z M
      R ≠ 0 ∧
        (∀ i : Fin 3, aeval z (Y i.castSucc) = algebraMap E G (V i) * R ^ d) ∧
        aeval z (Y (Fin.last 3)) = algebraMap E G a * R ^ d +
          algebraMap E G b * R ^ (d - 1) * aeval z L := by
  classical
  have hmz : aeval z M ≠ 0 := fun hz => hm ((hrel M d hM).mpr hz)
  have hnum : aeval x (N * L) ≠ 0 := by
    intro hz
    apply hr
    rw [hroot, ← map_mul, hz, zero_div]
  have hnumz : aeval z N * aeval z L ≠ 0 := by
    rw [← map_mul]
    exact fun hz => hnum ((hrel (N * L) (d + 1) (hN.mul hL)).mpr hz)
  refine ⟨hmz, div_ne_zero hnumz hmz, ?_, ?_⟩
  · intro i
    let P := Y i.castSucc * M ^ d - C (V i) * (N * L) ^ d
    have hP : P.IsHomogeneous (d * (d + 1)) := by
      have hleft : (Y i.castSucc * M ^ d).IsHomogeneous (d * (d + 1)) := by
        convert (hY i.castSucc).mul (hM.pow d) using 1 <;> ring
      have hright : (C (V i) * (N * L) ^ d).IsHomogeneous (d * (d + 1)) := by
        convert ((hN.mul hL).pow d).C_mul (V i) using 1 <;> ring
      exact hleft.sub hright
    have hPx : aeval x P = 0 := by
      simp only [P, map_sub, map_mul, map_pow, aeval_C]
      rw [hfirst, hroot, div_pow]
      field_simp [hm]
      ring
    have hPz := (hrel P (d * (d + 1)) hP).mp hPx
    have he : aeval z (Y i.castSucc) * aeval z M ^ d =
        algebraMap E G (V i) * (aeval z N * aeval z L) ^ d := by
      exact sub_eq_zero.mp (by simpa only [P, map_sub, map_mul, map_pow, aeval_C] using hPz)
    rw [div_pow, ← mul_div_assoc]
    exact (eq_div_iff (pow_ne_zero d hmz)).mpr he
  · let P := Y (Fin.last 3) * M ^ d -
        (C a * (N * L) ^ d + C b * (N * L) ^ (d - 1) * L * M)
    have hP := rational_cone_last_cleared_polynomial_homogeneous
      (Y (Fin.last 3)) N M L hd (hY _) hN hM hL a b
    have hPx : aeval x P = 0 := by
      simp only [P, map_sub, map_add, map_mul, map_pow, aeval_C, sub_eq_zero]
      apply (rational_cone_last_coordinate_iff_cleared _ _ _ _ _ _ hd hm).mp
      rw [← hroot]
      exact hlast
    have hPz := (hrel P (d * (d + 1)) hP).mp hPx
    apply (rational_cone_last_coordinate_iff_cleared _ _ _ _ _ _ hd hmz).mpr
    exact sub_eq_zero.mp (by simpa only [P, map_sub, map_add, map_mul, map_pow, aeval_C] using hPz)

end DimensionFourDependence
