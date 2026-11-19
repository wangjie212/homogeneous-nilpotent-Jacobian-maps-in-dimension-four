import DimensionFourDependence.ParabolaCoordinateAlgebra
import DimensionFourDependence.ProjectiveBoundaryProjection

/-! # An actual parabola determines every rational direction at infinity

The two independent coefficient directions give a left inverse. Its
two affine coordinates recover the parameter and its square. Their
homogeneous quadratic relation kills the linear-parameter coordinate
at infinity; the remaining linear relations recover the entire boundary
vector as a nonzero multiple of the quadratic direction.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

variable {E F κ : Type*} [Field E] [Field F] [Field κ] [Algebra E F] [Algebra E κ]

/-- Every nonzero extension-field direction at infinity of the
actual parabola is a nonzero multiple of its quadratic coefficient
direction. No infinity-support or degree assumption is supplied. -/
theorem actual_parabola_infinity_direction_multiple_quadratic_direction
    (x : Fin 4 → F) (a b c : Fin 4 → E) (hbc : LinearIndependent E ![b, c])
    (t : F) (hx : ∀ i, x i = algebraMap E F (a i) + algebraMap E F (b i) * t +
      algebraMap E F (c i) * t ^ 2)
    (v : Fin 4 → κ) (hv : v ≠ 0)
    (hpoint : projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 v)
      (by intro h; exact hv (funext (fun i => congrFun h (some i)))) ∈
        projectiveClosureSet (L := E) x) :
    ∃ r : κ, r ≠ 0 ∧ ∀ i, v i = r * algebraMap E κ (c i) := by
  classical
  obtain ⟨C, hC⟩ := directionPlaneMatrix_has_left_inverse b c hbc
  have hCb (j : Fin 2) : ∑ i : Fin 4, C j i * b i = if j = 0 then 1 else 0 := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) E => M j 0) hC
    simpa [Matrix.mul_apply, directionPlaneMatrix, Matrix.one_apply] using he
  have hCc (j : Fin 2) : ∑ i : Fin 4, C j i * c i = if j = 1 then 1 else 0 := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) E => M j 1) hC
    simpa [Matrix.mul_apply, directionPlaneMatrix, Matrix.one_apply] using he
  let U (i : Fin 4) : MvPolynomial (Option (Fin 4)) E := X (some i) - MvPolynomial.C (a i) * X none
  let T (j : Fin 2) : MvPolynomial (Option (Fin 4)) E := ∑ i, MvPolynomial.C (C j i) * U i
  have hU (i : Fin 4) : (U i).IsHomogeneous 1 :=
    (isHomogeneous_X (R := E) (some i)).sub (isHomogeneous_C_mul_X _ _)
  have hT (j : Fin 2) : (T j).IsHomogeneous 1 := by
    exact IsHomogeneous.sum _ _ _ (fun i _ => (hU i).C_mul (C j i))
  have hTx (j : Fin 2) : aeval (fun k : Option (Fin 4) => k.elim 1 x) (T j) =
      algebraMap E F (if j = 0 then 1 else 0) * t +
        algebraMap E F (if j = 1 then 1 else 0) * t ^ 2 := by
    change aeval _ (∑ i, MvPolynomial.C (C j i) * U i) = _
    simp only [map_sum, map_mul, aeval_C]
    have hu (i : Fin 4) : aeval (fun k : Option (Fin 4) => k.elim 1 x) (U i) =
        algebraMap E F (b i) * t + algebraMap E F (c i) * t ^ 2 := by
      simp only [U, map_sub, map_mul, aeval_X, aeval_C, Option.elim_some, Option.elim_none, mul_one]
      rw [hx i]
      ring
    simp only [hu, mul_add, ← mul_assoc, ← map_mul, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← map_sum, hCb, hCc]
  have hTx0 : aeval (fun k : Option (Fin 4) => k.elim 1 x) (T 0) = t := by simpa using hTx 0
  have hTx1 : aeval (fun k : Option (Fin 4) => k.elim 1 x) (T 1) = t ^ 2 := by simpa using hTx 1
  let τ : κ := ∑ i, algebraMap E κ (C 0 i) * v i
  let υ : κ := ∑ i, algebraMap E κ (C 1 i) * v i
  have hTv (j : Fin 2) : aeval (fun k : Option (Fin 4) => k.elim 0 v) (T j) =
      ∑ i, algebraMap E κ (C j i) * v i := by
    simp [T, U]
  let Q := T 0 ^ 2 - X none * T 1
  have hQ : Q.IsHomogeneous 2 := by
    exact ((hT 0).pow 2).sub ((isHomogeneous_X (R := E) none).mul (hT 1))
  have hQmem : Q ∈ projectiveConeIdeal (L := E) x := by
    apply (projectiveConeIdeal_mem_of_isHomogeneous x hQ).mpr
    simp only [Q, map_sub, map_pow, map_mul, aeval_X, Option.elim_none, hTx0, hTx1, one_mul, sub_self]
  have hτ : τ = 0 := by
    have he := projectiveClosureSet_extension_coordinate_equation x _ _ hpoint hQ hQmem
    have he' : τ ^ 2 = 0 := by
      simpa only [Q, map_sub, map_pow, map_mul, aeval_X, Option.elim_none, zero_mul, sub_zero, hTv] using he
    exact (pow_eq_zero_iff'.mp he').1
  have hrep (i : Fin 4) : v i = υ * algebraMap E κ (c i) := by
    let L := U i - MvPolynomial.C (b i) * T 0 - MvPolynomial.C (c i) * T 1
    have hL : L.IsHomogeneous 1 := ((hU i).sub ((hT 0).C_mul (b i))).sub ((hT 1).C_mul (c i))
    have hLmem : L ∈ projectiveConeIdeal (L := E) x := by
      apply (projectiveConeIdeal_mem_of_isHomogeneous x hL).mpr
      simp only [L, U, map_sub, map_mul, aeval_X, aeval_C, Option.elim_some,
        Option.elim_none, mul_one, hTx0, hTx1]
      rw [hx i]
      ring
    have he := projectiveClosureSet_extension_coordinate_equation x _ _ hpoint hL hLmem
    have he' : v i - algebraMap E κ (b i) * τ - algebraMap E κ (c i) * υ = 0 := by
      simpa only [L, U, map_sub, map_mul, aeval_X, aeval_C, Option.elim_some,
        Option.elim_none, mul_zero, sub_zero, hTv] using he
    rw [hτ, mul_zero, sub_zero] at he'
    exact (sub_eq_zero.mp he').trans (mul_comm _ _)
  refine ⟨υ, ?_, hrep⟩
  intro hzero
  apply hv
  funext i
  simpa only [hzero, zero_mul, Pi.zero_apply] using hrep i

end DimensionFourDependence
