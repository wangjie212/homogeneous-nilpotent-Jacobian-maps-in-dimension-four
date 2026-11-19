import DimensionFourDependence.HomogeneousCoefficientEuler
import DimensionFourDependence.RadialDerivativeIdentities
import DimensionFourDependence.WeightedQuadratic

/-! # The actual weights of the first two fiber invariants

The coefficients `h,c,q` in the constructed fiber equations have output
Euler weights `1,1/d,2/d-1`, as used at the start of Section 3.2.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

attribute [local instance] coefficientFieldScalarTower

section

variable (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "F" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) F (H (p (Fin.castSucc i))))
local notation "L" => coefficientField (K := K) Y

include hd hH

/-- The source Euler derivative of the first invariant is the invariant itself. -/
theorem firstFiberInvariant_sourceEuler (h : L)
    (hh : (h : F) = algebraMap (MvPolynomial (Fin 4) K) F (H (p 3))) :
    sourceEuler (K := K) (firstFiberInvariantInChart p Y hY h) = firstFiberInvariantInChart p Y hY h := by
  have hhe := homogeneous_last_output_euler H hd hH p hY h hh
  have hg (i : Fin 3) : sourceEuler (K := K) (coefficientPartial Y hY i h : F) = 0 := by
    rw [homogeneous_sourceEuler_coefficientEuler H hH p hY,
      coefficientGradient_euler_zero Y hY h hhe i]
    simp
  unfold firstFiberInvariantInChart
  rw [map_sub, map_sum, sourceEuler_coordinate]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [(sourceEuler (K := K)).leibniz, hg, smul_zero, add_zero, sourceEuler_coordinate]
  rfl

/-- The first invariant has output Euler weight `1/d`. -/
theorem firstFiberInvariant_output_weight (h c : L)
    (hh : (h : F) = algebraMap (MvPolynomial (Fin 4) K) F (H (p 3)))
    (hc : (c : F) = firstFiberInvariantInChart p Y hY h) :
    coefficientEuler Y hY c = algebraMap K L ((d : K)⁻¹) * c := by
  apply homogeneous_coefficientEuler_of_source_weight H hd hH p hY c ((d : K)⁻¹)
  have hce : sourceEuler (K := K) (c : F) = (c : F) := by
    rw [hc, firstFiberInvariant_sourceEuler H hd hH p hY h hh]
  rw [hce, map_inv₀, map_natCast, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (show d ≠ 0 by omega)), one_mul]

omit hd in
/-- A coefficient partial of a weight-`w` element has the corresponding source Euler weight. -/
theorem coefficientPartial_source_weight (a : L) (w : K)
    (ha : coefficientEuler Y hY a = algebraMap K L w * a) (i : Fin 3) :
    sourceEuler (K := K) (coefficientPartial Y hY i a : F) =
      (d : F) * algebraMap K F (w - 1) * (coefficientPartial Y hY i a : F) := by
  rw [homogeneous_sourceEuler_coefficientEuler H hH p hY,
    coefficientEuler_partial_weight Y hY a w ha i]
  change (d : F) * algebraMap L F (algebraMap K L (w - 1) * coefficientPartial Y hY i a) = _
  rw [map_mul, ← IsScalarTower.algebraMap_apply K L F]
  simp only [IntermediateField.algebraMap_apply]
  ring

/-- The second invariant has source Euler weight `2-d`. -/
theorem secondFiberInvariant_source_weight (h c : L)
    (hh : (h : F) = algebraMap (MvPolynomial (Fin 4) K) F (H (p 3)))
    (hc : (c : F) = firstFiberInvariantInChart p Y hY h) :
    sourceEuler (K := K) (secondFiberInvariant p Y hY h c) =
      (2 - (d : F)) * secondFiberInvariant p Y hY h c := by
  have hhe := homogeneous_last_output_euler H hd hH p hY h hh
  have hce := firstFiberInvariant_output_weight H hd hH p hY h c hh hc
  apply quadraticExpression_euler_weight
  · intro i
    rw [coefficientPartial_source_weight H hH p hY c ((d : K)⁻¹) hce i,
      map_sub, map_inv₀, map_natCast, map_one]
    have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hd0]
    ring
  · intro i j
    change sourceEuler (K := K) (coefficientHessian Y hY h i j : F) = _
    rw [homogeneous_sourceEuler_coefficientEuler H hH p hY,
      coefficientHessian_euler_negative Y hY h hhe i j]
    change (d : F) * (-(coefficientHessian Y hY h i j : F)) = _
    change (d : F) * (-(fiberHessian Y hY h i j)) = _
    ring
  · intro i
    exact sourceEuler_coordinate _

/-- The second invariant has output Euler weight `2/d-1`. -/
theorem secondFiberInvariant_output_weight (h c q : L)
    (hh : (h : F) = algebraMap (MvPolynomial (Fin 4) K) F (H (p 3)))
    (hc : (c : F) = firstFiberInvariantInChart p Y hY h)
    (hq : (q : F) = secondFiberInvariant p Y hY h c) :
    coefficientEuler Y hY q = algebraMap K L (2 * (d : K)⁻¹ - 1) * q := by
  apply homogeneous_coefficientEuler_of_source_weight H hd hH p hY q (2 * (d : K)⁻¹ - 1)
  have hqe : sourceEuler (K := K) (q : F) = (2 - (d : F)) * (q : F) := by
    rw [hq, secondFiberInvariant_source_weight H hd hH p hY h c hh hc]
  rw [hqe, map_sub, map_mul, map_ofNat, map_inv₀, map_natCast, map_one]
  have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hd0]

end

end DimensionFourDependence
