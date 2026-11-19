import DimensionFourDependence.AffineHyperplane
import DimensionFourDependence.AffinePrincipalCone

/-! # Solving a genuine two-coordinate affine-linear relation

If one coordinate is transcendental, a nonzero affine-linear relation
must have nonzero coefficient on the other coordinate. Solving it gives
the actual affine-linear expression over the original coefficient field.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

/-- A nonzero affine-linear relation with a transcendental coordinate
solves the other coordinate over the original coefficient field. -/
theorem affine_two_coordinate_relation_solve
    (t y : F) (ht : Transcendental L t)
    (Q : MvPolynomial (Option Unit) L) (hQ0 : Q ≠ 0) (hQ : Q.totalDegree ≤ 1)
    (hvalue : aeval (fun j : Option Unit => j.elim y (fun _ => t)) Q = 0) :
    ∃ a b : L, y = algebraMap L F a + algebraMap L F b * t := by
  let c0 := Q.coeff 0
  let cy := (pderiv none Q).coeff 0
  let ct := (pderiv (some ()) Q).coeff 0
  have hexp : Q = C c0 + C cy * X none + C ct * X (some ()) := by
    simpa [Fintype.sum_option, add_assoc, c0, cy, ct] using affine_polynomial_expansion Q hQ
  have hrel : algebraMap L F c0 + algebraMap L F cy * y + algebraMap L F ct * t = 0 := by
    rw [hexp] at hvalue
    simpa only [map_add, map_mul, aeval_C, aeval_X, Option.elim_none, Option.elim_some] using hvalue
  have hcy : cy ≠ 0 := by
    intro hzero
    have he : algebraMap L F c0 + algebraMap L F ct * t = 0 := by
      simpa only [hzero, map_zero, zero_mul, add_zero] using hrel
    have hpoly : Polynomial.C c0 + Polynomial.C ct * Polynomial.X = (0 : Polynomial L) := by
      apply transcendental_iff_injective.mp ht
      simpa using he
    have hc0 : c0 = 0 := by simpa using congrArg (fun P : Polynomial L => P.coeff 0) hpoly
    have hct : ct = 0 := by simpa using congrArg (fun P : Polynomial L => P.coeff 1) hpoly
    apply hQ0
    rw [hexp, hc0, hzero, hct]
    simp
  refine ⟨-c0 / cy, -ct / cy, ?_⟩
  have hcyF : algebraMap L F cy ≠ 0 := (map_ne_zero (algebraMap L F)).mpr hcy
  rw [map_div₀, map_div₀, map_neg, map_neg]
  field_simp
  linear_combination hrel

end DimensionFourDependence
