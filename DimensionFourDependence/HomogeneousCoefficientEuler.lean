import DimensionFourDependence.SourceEuler
import DimensionFourDependence.CoefficientEuler

/-! # Restricting the homogeneous source Euler field to the coefficient field

For degree `d` outputs the ordinary source Euler field restricts to `d`
times the output Euler field. Thus the last output has output weight one.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

attribute [local instance] coefficientFieldScalarTower

theorem homogeneous_sourceEuler_coefficientEuler
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hH : IsHomogMap H d)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (a : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) :
    sourceEuler (K := K) (a : FractionRing (MvPolynomial (Fin 4) K)) =
      (d : FractionRing (MvPolynomial (Fin 4) K)) * (coefficientEuler _ hY a : FractionRing (MvPolynomial (Fin 4) K)) := by
  apply source_derivation_coefficientEuler
  intro i
  exact sourceEuler_homogeneous _ (hH (p i.castSucc))

/-- A source Euler weight `d*w` is exactly output Euler weight `w`. -/
theorem homogeneous_coefficientEuler_of_source_weight
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (a : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc)))) (w : K)
    (ha : sourceEuler (K := K) (a : FractionRing (MvPolynomial (Fin 4) K)) =
      (d : FractionRing (MvPolynomial (Fin 4) K)) * algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) w * a) :
    coefficientEuler _ hY a = algebraMap K _ w * a := by
  apply (algebraMap _ (FractionRing (MvPolynomial (Fin 4) K))).injective
  rw [map_mul, ← IsScalarTower.algebraMap_apply K _ (FractionRing (MvPolynomial (Fin 4) K))]
  apply mul_left_cancel₀ (show (d : FractionRing (MvPolynomial (Fin 4) K)) ≠ 0 from
    Nat.cast_ne_zero.mpr (by omega))
  simp only [IntermediateField.algebraMap_apply]
  rw [← homogeneous_sourceEuler_coefficientEuler H hH p hY a, ha]
  ring

/-- The last homogeneous output has weight one in the actual algebraic coefficient field. -/
theorem homogeneous_last_output_euler
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (h : coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))
    (hh : (h : FractionRing (MvPolynomial (Fin 4) K)) = algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p 3))) : coefficientEuler _ hY h = h := by
  have he := homogeneous_coefficientEuler_of_source_weight H hd hH p hY h 1 (by
    rw [map_one, mul_one, hh, sourceEuler_homogeneous _ (hH (p 3))])
  simpa only [map_one, one_mul] using he

end DimensionFourDependence
