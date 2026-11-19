import DimensionFourDependence.MovingPlaneLowestCoefficient

/-! # The genuine binary equation on a moving projective line

The original ternary equation is restricted to the entire line
W=aY+bZ. The canonical binary restriction remains homogeneous and
evaluates to the original equation at every actual line point. A
transcendental coefficient ratio makes that restriction nonzero.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The original equation restricted to the entire specified moving line. -/
noncomputable def movingPlaneBinaryRestriction (a b : L)
    (P : MvPolynomial (Option (Fin 2)) K) : MvPolynomial (Fin 2) L :=
  aeval (fun o : Option (Fin 2) => o.elim (X 1)
    (![X 0, C a * X 0 + C b * X 1] : Fin 2 → MvPolynomial (Fin 2) L)) P

/-- The actual binary restriction has the same homogeneous degree
as the original ternary equation. -/
theorem movingPlaneBinaryRestriction_isHomogeneous (a b : L)
    (P : MvPolynomial (Option (Fin 2)) K) {D : ℕ} (hP : P.IsHomogeneous D) :
    (movingPlaneBinaryRestriction a b P).IsHomogeneous D := by
  apply (show (aeval (fun o : Option (Fin 2) => o.elim (X 1)
    (![X 0, C a * X 0 + C b * X 1] : Fin 2 → MvPolynomial (Fin 2) L)) P).IsHomogeneous D from ?_)
  have hlinear : ∀ o : Option (Fin 2),
      (o.elim (X 1) (![X 0, C a * X 0 + C b * X 1] : Fin 2 → MvPolynomial (Fin 2) L)).IsHomogeneous 1 := by
    intro o
    cases o with
    | none => exact isHomogeneous_X (R := L) 1
    | some i =>
      fin_cases i
      · exact isHomogeneous_X (R := L) 0
      · exact (isHomogeneous_C_mul_X a 0).add (isHomogeneous_C_mul_X b 1)
  simpa only [one_mul] using hP.aeval _ hlinear

variable {A : Type*} [CommRing A] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

/-- Evaluating the entire binary restriction is the original equation
at the specified actual point of the moving line. -/
theorem movingPlaneBinaryRestriction_aeval (a b : L)
    (P : MvPolynomial (Option (Fin 2)) K) (v : Fin 2 → A) :
    aeval v (movingPlaneBinaryRestriction a b P) =
      aeval (fun o : Option (Fin 2) => o.elim (v 1)
        (![v 0, algebraMap L A a * v 0 + algebraMap L A b * v 1] : Fin 2 → A)) P := by
  let q : Option (Fin 2) → MvPolynomial (Fin 2) L := fun o => o.elim (X 1)
    (![X 0, C a * X 0 + C b * X 1] : Fin 2 → MvPolynomial (Fin 2) L)
  have he := comp_aeval_apply q ((aeval v : MvPolynomial (Fin 2) L →ₐ[L] A).restrictScalars K) P
  have hcoords : (fun o => aeval v (q o)) =
      (fun o : Option (Fin 2) => o.elim (v 1)
        (![v 0, algebraMap L A a * v 0 + algebraMap L A b * v 1] : Fin 2 → A)) := by
    funext o
    cases o with
    | none => simp [q]
    | some i => fin_cases i <;> simp [q]
  simpa only [AlgHom.restrictScalars_apply, hcoords, movingPlaneBinaryRestriction, q] using he

omit [CommRing A] [Algebra L A] [Algebra K A] [IsScalarTower K L A] in
/-- A transcendental coefficient ratio excludes identical vanishing
of the original proper homogeneous locus on the entire moving line. -/
theorem movingPlaneBinaryRestriction_ne_zero [Infinite K]
    (a b : L) (ha : Transcendental K a)
    (P : MvPolynomial (Option (Fin 2)) K) (hP0 : P ≠ 0)
    {D : ℕ} (hP : P.IsHomogeneous D) : movingPlaneBinaryRestriction a b P ≠ 0 := by
  intro hz
  have he := movingPlaneBinaryRestriction_aeval a b P (![1, Polynomial.X] : Fin 2 → Polynomial L)
  have hcoords : (fun o : Option (Fin 2) => o.elim ((![1, Polynomial.X] : Fin 2 → Polynomial L) 1)
      (![(![1, Polynomial.X] : Fin 2 → Polynomial L) 0,
        algebraMap L (Polynomial L) a * (![1, Polynomial.X] : Fin 2 → Polynomial L) 0 +
        algebraMap L (Polynomial L) b * (![1, Polynomial.X] : Fin 2 → Polynomial L) 1] :
        Fin 2 → Polynomial L)) =
      (fun o : Option (Fin 2) => o.elim Polynomial.X
        (![1, Polynomial.C a + Polynomial.C b * Polynomial.X] : Fin 2 → Polynomial L)) := by
    funext o
    cases o with
    | none => simp
    | some i => fin_cases i <;> simp
  rw [hcoords, hz, map_zero] at he
  exact transcendental_moving_plane_affine_restriction_ne_zero a b ha P hP0 hP he.symm

end DimensionFourDependence
