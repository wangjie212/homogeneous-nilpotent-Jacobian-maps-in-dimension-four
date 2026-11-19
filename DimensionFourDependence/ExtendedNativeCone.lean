import DimensionFourDependence.ProjectiveConeFractionConstants
import DimensionFourDependence.ExtendedOwnCoordinateFieldGeneration
import DimensionFourDependence.ExtendedInputLinearCoefficient

/-! # The radial cone of the paper's actual normalized pencil -/

namespace DimensionFourDependence

open AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
  (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
  (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
  [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
  {d : ℕ} (hH : IsHomogMap H d)
  (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "s₀" => finSuccEquiv' (0 : Fin 4)
local notation "x₀" => (fun i : Fin 3 => w ((s₀).symm (some i)))

local instance extendedNativeConeIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance extendedNativeConeAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- The actual radial cone algebra of the original normalized pencil,
formed from its actual native affine coordinates and original constants. -/
@[reducible]
noncomputable def extendedClosedGaussNativeConeAlgebra : Subalgebra E (Polynomial (N).functionField) :=
  projectiveConeCoordinateAlgebra (E := E) x₀

local notation "A₀" => extendedClosedGaussNativeConeAlgebra H I E hH e

/-- The original four homogeneous source labels on the actual radial cone. -/
noncomputable def extendedClosedGaussNativeConeCoordinate (i : Fin 4) : A₀ :=
  projectiveConeCoordinate (E := E) x₀ ((s₀) i)

/-- The omitted-coordinate notation recovers the actual four native
weights in their original order, with the original zeroth weight one. -/
theorem extendedClosedGaussNativeCone_option_coordinate (i : Fin 4) :
    ((s₀) i).elim 1 x₀ = w i := by
  have h := projective_option_elim_ratios w s₀
    (extendedClosedGaussNormalizationHyperplaneWeight_ne_zero H I E hH e _) i
  simpa only [finSuccEquiv'_symm_none, extendedClosedGaussNormalizationHyperplaneWeight_zero, div_one] using h

/-- Every original homogeneous cone coordinate is its actual native
weight times the same original radial polynomial parameter. -/
theorem extendedClosedGaussNativeConeCoordinate_polynomial_value (i : Fin 4) :
    (extendedClosedGaussNativeConeCoordinate H I E hH e i : Polynomial (N).functionField) =
      Polynomial.C (w i) * Polynomial.X :=
  (projectiveConeCoordinate_polynomial_value x₀ ((s₀) i)).trans
    (congrArg (fun v : (N).functionField => Polynomial.C v * Polynomial.X)
      (extendedClosedGaussNativeCone_option_coordinate H I E hH e i))

/-- This actual cone is an actual finite-type algebra over the
original extended coefficient field. -/
theorem extendedClosedGaussNativeConeAlgebra_finiteType : Algebra.FiniteType E A₀ :=
  projectiveConeCoordinateAlgebra_finiteType x₀

/-- Its dimension is at least two, derived from the original
Gauss-dimension-one map and the actual affine surface coordinates. -/
theorem extendedClosedGaussNativeConeAlgebra_trdeg_at_least_two
    (hGauss : gaussImageDimension H I = 1) : 2 ≤ Algebra.trdeg E A₀ :=
  (extendedClosedGaussNormalization_original_affine_algebra_trdeg_two H I E hH e hGauss).symm.trans_le
    (projectiveConeCoordinateAlgebra_trdeg_ge_chart x₀)

/-- The actual normalization function field lifts as the original
degree-zero constant field inside the actual cone fraction field. -/
noncomputable def extendedClosedGaussNativeConeConstantHom : (N).functionField →ₐ[E] FractionRing A₀ :=
  projectiveConeFractionConstantHom x₀
    (extendedClosedGaussNormalization_original_affine_field_top H I E hH e)

/-- The actual constant lift has exactly its original native
field value under the original cone embedding. -/
theorem extendedClosedGaussNativeConeConstantHom_value (u : (N).functionField) :
    projectiveConeFractionEmbedding (E := E) x₀
      (extendedClosedGaussNativeConeConstantHom H I E hH e u) = RatFunc.C u :=
  projectiveConeFractionConstantHom_value x₀
    (extendedClosedGaussNormalization_original_affine_field_top H I E hH e) u

/-- Each actual native coordinate lifts to its original cone
coordinate divided by the same original radial coordinate. -/
theorem extendedClosedGaussNativeConeConstantHom_mul_radial_coordinate (i : Fin 4) :
    extendedClosedGaussNativeConeConstantHom H I E hH e (w i) *
      algebraMap A₀ (FractionRing A₀) (projectiveConeCoordinate (E := E) x₀ none) =
        algebraMap A₀ (FractionRing A₀) (extendedClosedGaussNativeConeCoordinate H I E hH e i) := by
  have h := projectiveConeFractionConstantHom_mul_radial_coordinate x₀
    (extendedClosedGaussNormalization_original_affine_field_top H I E hH e) ((s₀) i)
  exact (congrArg (fun u : (N).functionField =>
    extendedClosedGaussNativeConeConstantHom H I E hH e u *
      algebraMap A₀ (FractionRing A₀) (projectiveConeCoordinate (E := E) x₀ none))
      (extendedClosedGaussNativeCone_option_coordinate H I E hH e i).symm).trans h

end DimensionFourDependence
