import DimensionFourDependence.CoordinateHessianDirection

/-! # Coordinate partials on further algebraic coefficient extensions

Isotropic directions may be algebraic over the actual coefficient field.
The extended partials are constructed uniquely, still commute, and give
the scalar-extended actual Hessian and cubic tensor.
-/

namespace DimensionFourDependence

variable {K : Type*} [Field K] [CharZero K]

section

variable (Y : Fin 3 → FractionRing (MvPolynomial (Fin 4) K)) (hY : AlgebraicIndependent K Y)
    (E : Type*) [Field E] [Algebra (coefficientField (K := K) Y) E] [Algebra K E]
    [IsScalarTower K (coefficientField (K := K) Y) E]
    [Algebra.IsAlgebraic (coefficientField (K := K) Y) E]

/-- The uniquely extended coordinate partial on a further algebraic field. -/
noncomputable def extendedCoefficientPartial (i : Fin 3) : Derivation K E E :=
  Classical.choose (existsUnique_derivation_extension_algebraic
    (K := K) (E := coefficientField (K := K) Y) (L := E) (coefficientPartial Y hY i))

theorem extendedCoefficientPartial_extends (i : Fin 3) (a : coefficientField (K := K) Y) :
    extendedCoefficientPartial Y hY E i (algebraMap (coefficientField (K := K) Y) E a) =
      algebraMap (coefficientField (K := K) Y) E (coefficientPartial Y hY i a) :=
  (Classical.choose_spec (existsUnique_derivation_extension_algebraic
    (K := K) (E := coefficientField (K := K) Y) (L := E) (coefficientPartial Y hY i))).1 a

theorem extendedCoefficientPartial_coordinate (i j : Fin 3) :
    extendedCoefficientPartial Y hY E i
      (algebraMap (coefficientField (K := K) Y) E (coefficientCoordinate (K := K) Y j)) =
      if j = i then 1 else 0 := by
  rw [extendedCoefficientPartial_extends]
  unfold coefficientCoordinate
  rw [coefficientPartial_coordinate]
  split_ifs <;> simp

theorem extendedCoefficientPartials_commute (i j : Fin 3) (a : E) :
    extendedCoefficientPartial Y hY E i (extendedCoefficientPartial Y hY E j a) =
      extendedCoefficientPartial Y hY E j (extendedCoefficientPartial Y hY E i a) := by
  apply derivation_extensions_commute (K := K) (E := coefficientField (K := K) Y)
    (coefficientPartial Y hY i) (coefficientPartial Y hY j)
  · exact extendedCoefficientPartial_extends Y hY E i
  · exact extendedCoefficientPartial_extends Y hY E j
  · exact coefficientPartials_commute Y hY i j
  · exact Algebra.IsAlgebraic.isAlgebraic

/-- The extended derivatives give the actual base-changed Hessian. -/
theorem extendedCoefficientPartial_hessian (h : coefficientField (K := K) Y) :
    derivationHessian (extendedCoefficientPartial Y hY E)
      (algebraMap (coefficientField (K := K) Y) E h) =
        (coefficientHessian Y hY h).map (algebraMap (coefficientField (K := K) Y) E) := by
  funext i j
  change extendedCoefficientPartial Y hY E i (extendedCoefficientPartial Y hY E j
    (algebraMap (coefficientField (K := K) Y) E h)) = _
  rw [extendedCoefficientPartial_extends, extendedCoefficientPartial_extends]
  rfl

/-- The third extended derivatives give the actual base-changed cubic tensor. -/
theorem extendedCoefficientPartial_cubic (h : coefficientField (K := K) Y) :
    derivationCubicTensor (extendedCoefficientPartial Y hY E)
      (algebraMap (coefficientField (K := K) Y) E h) =
        fun i j k => algebraMap (coefficientField (K := K) Y) E (coefficientCubicTensor Y hY h i j k) := by
  funext i j k
  change extendedCoefficientPartial Y hY E i (extendedCoefficientPartial Y hY E j
    (extendedCoefficientPartial Y hY E k (algebraMap (coefficientField (K := K) Y) E h))) = _
  rw [extendedCoefficientPartial_extends, extendedCoefficientPartial_extends,
    extendedCoefficientPartial_extends]
  rfl

end

end DimensionFourDependence
