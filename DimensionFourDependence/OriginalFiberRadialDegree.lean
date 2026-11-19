import DimensionFourDependence.NonzeroHyperplaneRadialDegree
import DimensionFourDependence.FirstInvariantChart

/-! # The original first invariant preserves the projective-source degree

The first invariant's nonzero constant recovers the affine homogenizing
coordinate by a linear form in the original four source coordinates.
Applying the proved entire graded quotient comparison gives the same
Hilbert function and degree on the actual radial projective-source image.
-/

namespace DimensionFourDependence

open MvPolynomial

attribute [local instance] coefficientFieldScalarTower MvPolynomial.gradedAlgebra

variable {L : Type*} [Field L]

/-- The original linear graph expression before subtracting its
specified nonzero affine-hyperplane constant. -/
noncomputable def graphRadialLinearPolynomial (p : Equiv.Perm (Fin 4)) (A : Fin 3 → L) :
    MvPolynomial (Fin 4) L := X (p 3) - ∑ i, C (A i) * X (p i.castSucc)

/-- The original graph expression is an actual homogeneous linear form. -/
theorem graphRadialLinearPolynomial_homogeneous (p : Equiv.Perm (Fin 4)) (A : Fin 3 → L) :
    (graphRadialLinearPolynomial p A).IsHomogeneous 1 := by
  apply (isHomogeneous_X L (p 3)).sub
  exact IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X (A i) (p i.castSucc))

variable {K : Type*} [Field K] [CharZero K]
    (p : Equiv.Perm (Fin 4))
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (h c : coefficientField (K := K) Y)

/-- The original first invariant supplies the actual constant
value of that original linear source form. -/
theorem actual_first_invariant_radial_linear_value
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p Y hY h) :
    aeval (rationalCoordinate (K := K) (n := 4))
      (graphRadialLinearPolynomial p (fun i => coefficientPartial Y hY i h)) =
        algebraMap (coefficientField (K := K) Y) (FractionRing (MvPolynomial (Fin 4) K)) c := by
  simp only [graphRadialLinearPolynomial, map_sub, map_sum, map_mul, aeval_X, aeval_C]
  exact hc.symm

/-- The actual affine closure and actual radial projective-source
image have the same Hilbert function in every homogeneous degree. -/
theorem actual_first_invariant_radial_hilbert_function
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p Y hY h)
    (hc0 : c ≠ 0) (n : ℕ) :
    projectiveHilbertFunction (projectiveConeIdeal (L := coefficientField (K := K) Y)
      (rationalCoordinate (K := K) (n := 4))) n =
      projectiveHilbertFunction (projectiveFieldPointIdeal (E := coefficientField (K := K) Y)
        (rationalCoordinate (K := K) (n := 4))).toIdeal n :=
  projectiveHilbertFunction_nonzero_hyperplane_radial _
    (graphRadialLinearPolynomial_homogeneous p (fun i => coefficientPartial Y hY i h)) c hc0 _
    (actual_first_invariant_radial_linear_value p Y hY h c hc) n

/-- The actual original curve's positive Hilbert degree is unchanged
by projection to the original projective source level. -/
theorem actual_first_invariant_radial_curve_degree
    (hc : (c : FractionRing (MvPolynomial (Fin 4) K)) = firstFiberInvariantInChart p Y hY h)
    (hc0 : c ≠ 0) (e : ℕ) :
    HasCurveHilbertDegree (projectiveConeIdeal (L := coefficientField (K := K) Y)
      (rationalCoordinate (K := K) (n := 4))) e ↔
      HasCurveHilbertDegree (projectiveFieldPointIdeal (E := coefficientField (K := K) Y)
        (rationalCoordinate (K := K) (n := 4))).toIdeal e := by
  simp only [HasCurveHilbertDegree, actual_first_invariant_radial_hilbert_function p Y hY h c hc hc0]

end DimensionFourDependence
