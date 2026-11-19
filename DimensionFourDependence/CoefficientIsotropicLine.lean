import DimensionFourDependence.HessianDirectionLine
import DimensionFourDependence.ExtendedCoefficientPartials

/-! # Lines obtained from algebraic directions of the actual image Hessian

The coordinate partials on a further algebraic extension are constructed,
and the radial radical is deduced from the actual weight-one identity.
Only rank, normalization and the two conditions (3.4) remain explicit.
-/

namespace DimensionFourDependence

open Matrix

variable {K : Type*} [Field K] [CharZero K]

section

variable (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)

local notation "L" => coefficientField (K := K) Y

variable (E : Type*) [Field E] [Algebra (coefficientField (K := K) Y) E]

/-- The actual Hessian's radial kernel is preserved over further fields. -/
theorem coefficientHessian_radial_mulVec_map
    (h : L) (hh : coefficientEuler Y hY h = h) :
    (coefficientHessian Y hY h).map (algebraMap L E) *ᵥ
      (fun i => algebraMap L E (coefficientCoordinate (K := K) Y i)) = 0 := by
  funext i
  change (∑ j, algebraMap L E (coefficientHessian Y hY h i j) *
    algebraMap L E (coefficientCoordinate (K := K) Y j)) = 0
  simp only [← map_mul, ← map_sum]
  have he : (∑ j, coefficientHessian Y hY h i j * coefficientCoordinate (K := K) Y j) = 0 := by
    calc
      (∑ j, coefficientHessian Y hY h i j * coefficientCoordinate (K := K) Y j) =
          ∑ j, coefficientCoordinate (K := K) Y j * coefficientHessian Y hY h j i := by
        apply Finset.sum_congr rfl
        intro j _
        rw [coefficientHessian_symmetric Y hY h i j, mul_comm]
      _ = 0 := coefficientHessian_radial_contraction Y hY h hh i
  rw [he, map_zero]

variable [CharZero E] [Algebra K E]
    [IsScalarTower K (coefficientField (K := K) Y) E]
    [Algebra.IsAlgebraic (coefficientField (K := K) Y) E]

/-- The differential-to-line step of Proposition 3.1 for the actual
coefficient Hessian and algebraic isotropic directions. Every image
equation vanishes identically on the resulting polynomial line. -/
theorem coefficient_normalized_isotropic_direction_line
    (h : L) (hh : coefficientEuler Y hY h = h)
    (hrank : ((coefficientHessian Y hY h).map (algebraMap L E)).rank = 2)
    (Z : Fin 3 → E) (a b : Fin 3)
    (hYa : algebraMap L E (coefficientCoordinate (K := K) Y a) ≠ 0)
    (hZa : Z a = 0) (hZb : Z b = 1)
    (hZ : matrixBilinearPairing ((coefficientHessian Y hY h).map (algebraMap L E)) Z Z = 0)
    (hCubic : (∑ i, ∑ j, ∑ k, algebraMap L E (coefficientCubicTensor Y hY h i j k) *
      Z i * Z j * Z k) = 0)
    (R : MvPolynomial (Fin 4) K)
    (hR : MvPolynomial.aeval (Fin.snoc (coefficientCoordinate (K := K) Y) h) R = 0) :
    MvPolynomial.aeval (fun j : Fin 4 =>
      Polynomial.C (Fin.snoc (fun i => algebraMap L E (coefficientCoordinate (K := K) Y i))
        (algebraMap L E h) j) +
      Polynomial.C (Fin.snoc Z (∑ i, Z i * algebraMap L E (coefficientGradient Y hY h i)) j) *
        Polynomial.X) R = 0 := by
  let δ := extendedCoefficientPartial Y hY E
  let y := fun i => algebraMap L E (coefficientCoordinate (K := K) Y i)
  have hHess : derivationHessian δ (algebraMap L E h) =
      (coefficientHessian Y hY h).map (algebraMap L E) := extendedCoefficientPartial_hessian Y hY E h
  have hCubic' : (∑ i, ∑ j, ∑ k,
      derivationCubicTensor δ (algebraMap L E h) i j k * Z i * Z j * Z k) = 0 := by
    simpa only [δ, extendedCoefficientPartial_cubic] using hCubic
  have hR' : MvPolynomial.aeval (Fin.snoc y (algebraMap L E h)) R = 0 := by
    have he := MvPolynomial.comp_aeval_apply (Fin.snoc (coefficientCoordinate (K := K) Y) h)
      (IsScalarTower.toAlgHom K L E) R
    rw [hR, map_zero] at he
    have hg : (fun j : Fin 4 => (IsScalarTower.toAlgHom K L E)
        ((Fin.snoc (coefficientCoordinate (K := K) Y) h : Fin 4 → L) j)) = Fin.snoc y (algebraMap L E h) := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.snoc_last]
        rfl
      · simp only [Fin.snoc_castSucc]
        rfl
    rw [hg] at he
    exact he.symm
  have hline := normalized_hessian_direction_line_identity δ
    (extendedCoefficientPartials_commute Y hY E) y (extendedCoefficientPartial_coordinate Y hY E)
    (algebraMap L E h) (by rw [hHess]; exact hrank) Z
    (by rw [hHess]; exact coefficientHessian_radial_mulVec_map Y hY E h hh)
    a b hYa hZa hZb (by rw [hHess]; exact hZ) hCubic' R hR'
  simpa only [δ, y, extendedCoefficientPartial_extends, coefficientGradient] using hline

end

end DimensionFourDependence
