import DimensionFourDependence.TangentPlaneSpan

/-! # Varying tangents over the actual coefficient field

The verified vertical derivation is made linear over its exact constant
field. Nonlinearity of the actual source coordinates over that field
then forces independence of the tangent and its derivative.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K] [CharZero K]

/-- The actual vertical derivation, now over its full coefficient field. -/
noncomputable def fiberTangentDerivation
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (hu : u ≠ 0)
    (hker : rationalJacobian Y *ᵥ u = 0) :
    Derivation (coefficientField (K := K) Y) (FractionRing (MvPolynomial (Fin 4) K))
      (FractionRing (MvPolynomial (Fin 4) K)) :=
  derivationOverConstantSubfield (sourceVectorDerivation u)
    ((coefficientField (K := K) Y).restrictScalars K)
    (le_of_eq (tangent_derivation_constants Y hY u hu hker).symm)

theorem fiberTangentDerivation_apply
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (hu : u ≠ 0)
    (hker : rationalJacobian Y *ᵥ u = 0) (z : FractionRing (MvPolynomial (Fin 4) K)) :
    fiberTangentDerivation Y hY u hu hker z = sourceVectorDerivation u z := rfl

/-- Its constants are actual scalars in the constructed coefficient field. -/
theorem fiberTangentDerivation_constant_scalar
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (hu : u ≠ 0)
    (hker : rationalJacobian Y *ᵥ u = 0) (z : FractionRing (MvPolynomial (Fin 4) K))
    (hz : fiberTangentDerivation Y hY u hu hker z = 0) :
    ∃ c : coefficientField (K := K) Y,
      algebraMap (coefficientField (K := K) Y) (FractionRing (MvPolynomial (Fin 4) K)) c = z := by
  have hm : z ∈ derivationConstants (sourceVectorDerivation u) := hz
  rw [tangent_derivation_constants Y hY u hu hker] at hm
  exact ⟨⟨z, hm⟩, rfl⟩

/-- A nonlinear actual fiber has independent tangent and tangent
derivative; the constant-field and tangent assertions are all derived. -/
theorem nonlinear_actual_fiber_tangent_independent
    (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (u : Fin 4 → FractionRing (MvPolynomial (Fin 4) K)) (hu : u ≠ 0)
    (hker : rationalJacobian Y *ᵥ u = 0)
    (hline : ¬ LiesInAffineLine (E := coefficientField (K := K) Y)
      (rationalCoordinate (K := K) (n := 4))) :
    LinearIndependent (FractionRing (MvPolynomial (Fin 4) K))
      ![(fun i => sourceVectorDerivation u (u i)), u] := by
  let D := fiberTangentDerivation Y hY u hu hker
  have hDu : (fun i => D (rationalCoordinate (K := K) i)) ≠ 0 := by
    simpa only [D, fiberTangentDerivation_apply, sourceVectorDerivation_coordinate] using hu
  have hvar := nonlinear_curve_tangent_derivative_independent D
    (rationalCoordinate (K := K) (n := 4))
    (fiberTangentDerivation_constant_scalar Y hY u hu hker) hDu hline
  simpa only [D, fiberTangentDerivation_apply, sourceVectorDerivation_coordinate] using hvar

end DimensionFourDependence
