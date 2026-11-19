import DimensionFourDependence.HomogeneousConeFormulaTransfer

/-! # The actual root power and scaled-plane alternative transfer to affine source

The root's specified output-linear power and the alternative proportional
plane identity have homogeneous cleared equations. They transfer with the
same exact source relations and the same nonzero denominator as the full
cone-coordinate formula.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000

variable {E F G : Type*} [Field E] [Field F] [Field G] [Algebra E F] [Algebra E G]

/-- Equality of homogeneous relations transfers the rational root's
actual output-linear power identity with its original denominator. -/
theorem homogeneous_relations_transfer_rational_root_power
    (N M S L : MvPolynomial (Fin 4) E) {d : ℕ}
    (hN : N.IsHomogeneous d) (hM : M.IsHomogeneous d) (hS : S.IsHomogeneous d)
    (hL : L.IsHomogeneous 1) (x : Fin 4 → F) (z : Fin 4 → G)
    (hrel : ∀ (P : MvPolynomial (Fin 4) E) (n : ℕ), P.IsHomogeneous n →
      (aeval x P = 0 ↔ aeval z P = 0))
    (r : F) (hm : aeval x M ≠ 0)
    (hroot : r = aeval x N * aeval x L / aeval x M)
    (hpower : r ^ d = aeval x S) :
    (aeval z N * aeval z L / aeval z M) ^ d = aeval z S := by
  have hmz : aeval z M ≠ 0 := fun hz => hm ((hrel M d hM).mpr hz)
  let P := (N * L) ^ d - S * M ^ d
  have hP : P.IsHomogeneous (d * (d + 1)) :=
    rationalRootClearedPolynomial_homogeneous N M S L hN hM hS hL
  have hclear := (rational_root_power_iff_cleared
    (aeval x N) (aeval x M) (aeval x S) (aeval x L) d hm).mp (by rw [← hroot]; exact hpower)
  have hPx : aeval x P = 0 := by
    simpa only [P, map_sub, map_pow, map_mul, sub_eq_zero] using hclear
  have hPz := (hrel P (d * (d + 1)) hP).mp hPx
  apply (rational_root_power_iff_cleared _ _ _ _ d hmz).mpr
  exact sub_eq_zero.mp (by simpa only [P, map_sub, map_pow, map_mul] using hPz)

/-- The remaining scaled-plane root alternative also transfers from
the native homogeneous source to the original affine source. -/
theorem homogeneous_relations_transfer_scaled_plane_root
    (N M L : MvPolynomial (Fin 4) E) {d : ℕ}
    (hN : N.IsHomogeneous d) (hM : M.IsHomogeneous d) (hL : L.IsHomogeneous 1)
    (x : Fin 4 → F) (z : Fin 4 → G)
    (hrel : ∀ (P : MvPolynomial (Fin 4) E) (n : ℕ), P.IsHomogeneous n →
      (aeval x P = 0 ↔ aeval z P = 0))
    (r : F) (hm : aeval x M ≠ 0)
    (hroot : r = aeval x N * aeval x L / aeval x M)
    (c : E) (hplane : r = algebraMap E F c * aeval x L) :
    aeval z N * aeval z L / aeval z M = algebraMap E G c * aeval z L := by
  have hmz : aeval z M ≠ 0 := fun hz => hm ((hrel M d hM).mpr hz)
  let P := N * L - C c * L * M
  have hright : (C c * L * M).IsHomogeneous (d + 1) := by
    convert (hL.C_mul c).mul hM using 1; omega
  have hP : P.IsHomogeneous (d + 1) := (hN.mul hL).sub hright
  have hclear := (div_eq_iff hm).mp (hroot.symm.trans hplane)
  have hPx : aeval x P = 0 := by
    simpa only [P, map_sub, map_mul, aeval_C, sub_eq_zero] using hclear
  have hPz := (hrel P (d + 1) hP).mp hPx
  apply (div_eq_iff hmz).mpr
  exact sub_eq_zero.mp (by simpa only [P, map_sub, map_mul, aeval_C] using hPz)

end DimensionFourDependence
