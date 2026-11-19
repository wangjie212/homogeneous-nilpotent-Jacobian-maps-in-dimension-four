import DimensionFourDependence.CharacteristicScaleCoefficientImages
import DimensionFourDependence.ScaledSourceRelativeCurveComparison

/-! # The actual characteristic pencil inherits the original radial fiber Hilbert bound -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra coefficientFieldScalarTower
attribute [local instance 2000] Algebra.toSMul

universe u

set_option quotPrecheck false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)
  (hd : 0 < d) (hind : ¬ComponentsDependent H) (hGauss : gaussImageDimension H I = 1)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "F₀" => (N).functionField
local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "T₀" => ∑ j, algebraMap E (F₀)
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0 j) * (w) j
local notation "t₀" r:max => nativeCharacteristicPencilValue H I E hH e hd hind hGauss r
local notation "C₀" r:max => pencilCoefficientCurveField (E := E) (t₀ r)

local instance characteristicPencilOriginalHilbertIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance characteristicPencilOriginalHilbertAlgebra : Algebra E (F₀) :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e
noncomputable local instance characteristicPencilOriginalHilbertOriginalAlgebra : Algebra K (F₀) :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

/-- Every homogeneous degree of the actual pencil curve over its
own relatively closed coefficient field is bounded by the original
radial generic fiber in any actual independent output chart. The
independent scale and all coefficient compatibilities are constructed. -/
theorem actual_characteristic_pencil_hilbert_le_original_radial_fiber
    (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      S₀ (H (p i.castSucc))))
    (cN : Fin 4 → E) (r : F₀)
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e hd hind hGauss cN r)
    (hT : (T₀) ≠ 0) (n : ℕ) :
    projectiveHilbertFunction (projectiveFieldPointIdeal (E := C₀ r) (w)).toIdeal n ≤
      projectiveHilbertFunction (projectiveFieldPointIdeal
        (E := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
          S₀ (H (p i.castSucc)))) (rationalCoordinate (K := K) (n := 4))).toIdeal n := by
  let B := IntermediateField.adjoin E {t₀ r}
  let L := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
    S₀ (H (p i.castSucc)))
  let Φ := nativeCharacteristicScaleSourceHom H I E hH e hd hind hGauss hT
  have hcoeff (c : L) : IsAlgebraic (IntermediateField.adjoin B {(RatFunc.X : RatFunc F₀)})
      (Φ (algebraMap L S₀ c)) :=
    actual_characteristic_scaled_original_fiber_coefficients_algebraic
      H I E hH e hd hind hGauss hrank p hY cN r hfactor hT c
  have hvalues (i : Fin 4) : Φ (rationalCoordinate (K := K) i) =
      RatFunc.X * RatFunc.C ((w) i / (T₀)) :=
    nativeCharacteristicScaleSourceHom_coordinate H I E hH e hd hind hGauss hT i
  have hb := scaled_source_relative_constant_closure_hilbert_bound
    (B := B) Φ.toRingHom hcoeff (rationalCoordinate (K := K) (n := 4))
    (fun i => (w) i / (T₀)) RatFunc.X RatFunc.X_ne_zero hvalues n
  have hnormalized : (fun i => (w) i / (T₀)) = (fun i => (T₀)⁻¹ * (w) i) := by
    funext i
    rw [div_eq_mul_inv, mul_comm]
  rw [hnormalized, projectiveFieldPointIdeal_scale (w) (T₀)⁻¹ (inv_ne_zero hT)] at hb
  exact hb

/-- The actual characteristic pencil's generic curve has degree
no larger than the original radial fiber, with both degrees measured
in their original projective source coordinates. -/
theorem actual_characteristic_pencil_curve_degree_le_original_radial_fiber
    (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      S₀ (H (p i.castSucc))))
    (cN : Fin 4 → E) (r : F₀)
    (hfactor : CharacteristicNativeRulingRootFactorization H I E hH e hd hind hGauss cN r)
    (hT : (T₀) ≠ 0) {D D' : ℕ}
    (hD : HasCurveHilbertDegree (projectiveFieldPointIdeal
      (E := coefficientField (K := K) (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
        S₀ (H (p i.castSucc)))) (rationalCoordinate (K := K) (n := 4))).toIdeal D)
    (hD' : HasCurveHilbertDegree (projectiveFieldPointIdeal (E := C₀ r) (w)).toIdeal D') : D' ≤ D :=
  curveHilbertDegree_le_of_hilbertFunction_le _ _
    (fun n => actual_characteristic_pencil_hilbert_le_original_radial_fiber
      H I E hH e hd hind hGauss hrank p hY cN r hfactor hT n) hD hD'

end DimensionFourDependence
