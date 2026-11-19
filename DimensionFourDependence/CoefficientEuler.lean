import DimensionFourDependence.EulerDerivation

/-! # Euler weights in the actual algebraic coefficient field

This identifies the output Euler vector field on the relative algebraic
closure and the restriction of any source derivation with equal output
weights. The coordinate partials are the already constructed extensions.
-/

namespace DimensionFourDependence

variable {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}

attribute [local instance] coefficientFieldScalarTower

/-- The independent output coordinates viewed in the coefficient field. -/
noncomputable def coefficientCoordinate (Y : Fin n → F) (i : Fin n) : coefficientField (K := K) Y :=
  algebraMap (IntermediateField.adjoin K (Set.range Y)) (coefficientField (K := K) Y)
    (outputCoordinate (K := K) Y i)

omit [CharZero K] in
theorem coefficientCoordinate_coe (Y : Fin n → F) (i : Fin n) :
    (coefficientCoordinate (K := K) Y i : F) = Y i := rfl

/-- The actual output Euler derivation on the algebraic coefficient field. -/
noncomputable def coefficientEuler (Y : Fin n → F) (hY : AlgebraicIndependent K Y) :
    Derivation K (coefficientField (K := K) Y) (coefficientField (K := K) Y) :=
  coordinateEuler (coefficientCoordinate (K := K) Y) (coefficientPartial (K := K) Y hY)

theorem coefficientEuler_apply (Y : Fin n → F) (hY : AlgebraicIndependent K Y)
    (a : coefficientField (K := K) Y) :
    coefficientEuler Y hY a = ∑ i, coefficientCoordinate (K := K) Y i * coefficientPartial Y hY i a :=
  coordinateEuler_apply _ _ _

theorem coefficientEuler_partial_weight (Y : Fin n → F) (hY : AlgebraicIndependent K Y)
    (a : coefficientField (K := K) Y) (w : K)
    (ha : coefficientEuler Y hY a = algebraMap K (coefficientField (K := K) Y) w * a) (j : Fin n) :
    coefficientEuler Y hY (coefficientPartial Y hY j a) =
      algebraMap K (coefficientField (K := K) Y) (w - 1) * coefficientPartial Y hY j a :=
  coordinateEuler_partial_weight _ _ (coefficientPartial_coordinate Y hY)
    (coefficientPartials_commute Y hY) a w ha j

/-- A source derivation giving all independent outputs weight `d`
restricts to `d` times the output Euler derivation on every algebraic coefficient. -/
theorem source_derivation_coefficientEuler
    (Y : Fin n → F) (hY : AlgebraicIndependent K Y) (D : Derivation K F F) (d : F)
    (hDY : ∀ i, D (Y i) = d * Y i) (a : coefficientField (K := K) Y) :
    D (a : F) = d * (coefficientEuler Y hY a : F) := by
  rw [coefficient_chain_rule Y hY, coefficientEuler_apply]
  change (∑ i, D (Y i) * (coefficientPartial Y hY i a : F)) =
    d * algebraMap (coefficientField (K := K) Y) F
      (∑ i, coefficientCoordinate (K := K) Y i * coefficientPartial Y hY i a)
  simp only [map_sum, map_mul, IntermediateField.algebraMap_apply,
    coefficientCoordinate_coe, Finset.mul_sum, hDY, mul_assoc]

end DimensionFourDependence
