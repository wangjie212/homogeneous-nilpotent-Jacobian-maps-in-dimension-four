import DimensionFourDependence.HomogeneousPolynomialLeadingCoefficient
import DimensionFourDependence.TranscendentalPolynomialParametrization
import DimensionFourDependence.ProjectiveBoundaryProjection

/-! # A polynomial curve's actual highest direction belongs to its projective closure -/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

variable {E F sigma : Type*} [Field E] [Field F] [Algebra E F]

/-- A nonzero highest polynomial coefficient vector at a positive
uniform degree is an actual point at infinity of the original
projective closure, for all its homogeneous relations. -/
theorem polynomial_parametrization_highest_direction_mem_projective_closure
    (x : sigma → F) (q : sigma → Polynomial E) (m : ℕ) (hm : 0 < m)
    (hq : ∀ i, (q i).natDegree ≤ m)
    (hv : (fun i => (q i).coeff m) ≠ 0)
    (t : F) (ht : Transcendental E t) (hx : ∀ i, Polynomial.aeval t (q i) = x i) :
    projectiveFieldPoint (E := E)
      (fun j : Option sigma => j.elim 0 (fun i => (q i).coeff m))
      (by intro h; exact hv (funext (fun i => congrFun h (some i)))) ∈
        projectiveClosureSet (L := E) x := by
  classical
  let w : Option sigma → Polynomial E := fun j => j.elim 1 q
  have hw (j : Option sigma) : (w j).natDegree ≤ m := by
    cases j with
    | none => simp [w]
    | some i => exact hq i
  have hwvalue (j : Option sigma) : Polynomial.aeval t (w j) = j.elim 1 x := by
    cases j with
    | none => simp [w]
    | some i => exact hx i
  have hwtop : (fun j => (w j).coeff m) =
      (fun j : Option sigma => j.elim 0 (fun i => (q i).coeff m)) := by
    funext j
    cases j with
    | none => simp only [w, Option.elim_none, Polynomial.coeff_one, Nat.ne_of_gt hm, ite_false]
    | some i => rfl
  rw [projectiveClosureSet_eq_zeroLocus_cone]
  intro P hP
  change projectiveFieldPointMap (E := E) _ P = 0
  apply Polynomial.ext
  intro D
  rw [projectiveFieldPointMap_coeff, Polynomial.coeff_zero]
  have hzero := (projectiveConeIdeal_mem_of_isHomogeneous x
    (homogeneousComponent_isHomogeneous D P)).mp
      (projectiveConeIdeal_homogeneousComponent_mem x hP D)
  have hid := original_polynomial_parametrization_constant_of_transcendental
    (K := E) t ht (fun j : Option sigma => j.elim 1 x) w hwvalue
      (homogeneousComponent D P) 0 (by simpa only [map_zero] using hzero)
  have he := congrArg (fun p : Polynomial E => p.coeff (m * D)) hid
  rw [homogeneous_aeval_coefficient_at_scaled_degree _
    (homogeneousComponent_isHomogeneous D P) w m hw, hwtop] at he
  simpa using he

/-- The quadratic direction of the given nondegenerate actual
parabola is itself an actual point at infinity of its projective
closure; neither boundary membership nor a valuation is supplied. -/
theorem actual_parabola_quadratic_direction_mem_projective_closure
    (x : Fin 4 → F) (a b c : Fin 4 → E) (hbc : LinearIndependent E ![b, c])
    (t : F) (ht : Transcendental E t)
    (hx : ∀ i, x i = algebraMap E F (a i) + algebraMap E F (b i) * t +
      algebraMap E F (c i) * t ^ 2) :
    projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 c)
      (by intro h; exact hbc.ne_zero 1 (funext (fun i => congrFun h (some i)))) ∈
        projectiveClosureSet (L := E) x := by
  let q : Fin 4 → Polynomial E := fun i =>
    Polynomial.C (a i) + Polynomial.C (b i) * Polynomial.X + Polynomial.C (c i) * Polynomial.X ^ 2
  have hq (i : Fin 4) : (q i).natDegree ≤ 2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le (by simp)
      exact Polynomial.natDegree_mul_le.trans (by simp)
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  have htop (i : Fin 4) : (q i).coeff 2 = c i := by simp [q]
  have hv : (fun i => (q i).coeff 2) ≠ 0 := by
    simpa [htop] using hbc.ne_zero 1
  have hvalue (i : Fin 4) : Polynomial.aeval t (q i) = x i := by
    simpa only [q, map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X] using (hx i).symm
  simpa only [htop] using polynomial_parametrization_highest_direction_mem_projective_closure
    x q 2 (by decide) hq hv t ht hvalue

end DimensionFourDependence
