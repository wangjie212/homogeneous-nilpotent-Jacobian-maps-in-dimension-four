import DimensionFourDependence.PolynomialCurveInfinity
import DimensionFourDependence.ParabolaInfinityDirection
import DimensionFourDependence.GraphBoundaryProportionality

/-! # The entire actual infinity support of a parabola is its quadratic direction

Every projective-spectrum prime has its own fraction-field coordinate
representative. The extension-field direction comparison identifies
that representative with the actual quadratic direction. Thus the
support statement covers all projective primes, without a closed-point
coverage assumption or an algebraically closed coefficient field.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

/-- Every prime of the actual projective closure's infinity
section is the same rational quadratic-direction point. -/
theorem actual_parabola_every_projective_infinity_prime_eq_quadratic_direction
    (x : Fin 4 → F) (a b c : Fin 4 → E) (hbc : LinearIndependent E ![b, c])
    (t : F) (hx : ∀ i, x i = algebraMap E F (a i) + algebraMap E F (b i) * t +
      algebraMap E F (c i) * t ^ 2)
    (z : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E))
    (hz : z ∈ projectiveClosureSet (L := E) x) (hinfinity : X none ∈ z.asHomogeneousIdeal) :
    z = projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 c)
      (by intro h; exact hbc.ne_zero 1 (funext (fun i => congrFun h (some i)))) := by
  let κ := FractionRing (MvPolynomial (Option (Fin 4)) E ⧸ z.asHomogeneousIdeal.toIdeal)
  let w : Option (Fin 4) → κ := projectivePrimeCoordinate z
  have hw : w ≠ 0 := projectivePrimeCoordinate_ne_zero z
  have hwzero : w none = 0 := (projectivePrimeCoordinate_eq_zero_iff z none).mpr hinfinity
  let v : Fin 4 → κ := fun i => w (some i)
  have hv : v ≠ 0 := by
    intro hzero
    apply hw
    funext j
    cases j with
    | none => exact hwzero
    | some i => exact congrFun hzero i
  have hcoord : w = (fun j : Option (Fin 4) => j.elim 0 v) := by
    funext j
    cases j with
    | none => exact hwzero
    | some i => rfl
  have heq : projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 v)
      (by intro h; exact hv (funext (fun i => congrFun h (some i)))) = z := by
    calc
      _ = projectiveFieldPoint (E := E) w hw :=
        projectiveFieldPoint_eq_of_coordinate_eq _ _ _ hw hcoord.symm
      _ = z := projectivePrimeCoordinate_represents z
  have hpoint : projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 v)
      (by intro h; exact hv (funext (fun i => congrFun h (some i)))) ∈ projectiveClosureSet (L := E) x := by
    rw [heq]
    exact hz
  obtain ⟨r, hr, hrep⟩ := actual_parabola_infinity_direction_multiple_quadratic_direction
    x a b c hbc t hx v hv hpoint
  have hc : c ≠ 0 := by simpa using hbc.ne_zero 1
  have hmul : v = r • (fun i => algebraMap E κ (c i)) := by
    funext i
    exact hrep i
  exact heq.symm.trans (projective_infinity_point_eq_of_mapped_direction_multiple c v hc hv r hr hmul)

/-- The actual set of all projective primes at infinity is exactly
the singleton quadratic-direction point. Its membership as well as
uniqueness are proved from the parametrization. -/
theorem actual_parabola_projective_infinity_support_eq_singleton
    (x : Fin 4 → F) (a b c : Fin 4 → E) (hbc : LinearIndependent E ![b, c])
    (t : F) (ht : Transcendental E t)
    (hx : ∀ i, x i = algebraMap E F (a i) + algebraMap E F (b i) * t +
      algebraMap E F (c i) * t ^ 2) :
    {z : ProjectiveSpectrum (homogeneousSubmodule (Option (Fin 4)) E) |
      z ∈ projectiveClosureSet (L := E) x ∧ X none ∈ z.asHomogeneousIdeal} =
    {projectiveFieldPoint (E := E) (fun j : Option (Fin 4) => j.elim 0 c)
      (by intro h; exact hbc.ne_zero 1 (funext (fun i => congrFun h (some i))))} := by
  ext z
  constructor
  · rintro ⟨hz, hinfinity⟩
    exact Set.mem_singleton_iff.mpr
      (actual_parabola_every_projective_infinity_prime_eq_quadratic_direction x a b c hbc t hx z hz hinfinity)
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    refine ⟨actual_parabola_quadratic_direction_mem_projective_closure x a b c hbc t ht hx, ?_⟩
    apply (projectiveFieldPoint_homogeneous_mem _ _ (X none) (isHomogeneous_X (R := E) none)).mpr
    simp only [aeval_X, Option.elim_none]

end DimensionFourDependence
