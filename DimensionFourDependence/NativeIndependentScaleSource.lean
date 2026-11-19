import DimensionFourDependence.NativeOriginalSourceFaithfulness
import DimensionFourDependence.IndependentScaleSourceEmbedding

/-! # The independently scaled native solution contains the original rational source -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

universe u

set_option quotPrecheck false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hH : IsHomogMap H d)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "N" => extendedClosedGaussNormalizationScheme H I E hH e
local notation "w" => extendedClosedGaussNormalizationHyperplaneWeight H I E hH e
local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E

local instance nativeIndependentScaleSourceIntegral : IsIntegral N :=
  extendedClosedGaussNormalizationScheme_isIntegral H I E hH e
noncomputable local instance nativeIndependentScaleSourceExtendedAlgebra : Algebra E (N).functionField :=
  extendedClosedGaussOwnFunctionFieldAlgebra H I E hH e

/-- Original coefficients enter the actual native source field by
the already specified closed Gauss coefficient extension. -/
@[instance_reducible]
noncomputable def extendedClosedGaussOriginalSourceAlgebra : Algebra K (N).functionField :=
  ((algebraMap E (N).functionField).comp (ι)).toAlgebra

noncomputable local instance nativeIndependentScaleSourceOriginalAlgebra : Algebra K (N).functionField :=
  extendedClosedGaussOriginalSourceAlgebra H I E hH e

variable (L : MvPolynomial (Fin 4) E)

/-- Normalizing the original native projective coordinates by a
nonzero original form preserves the absence of original homogeneous
source relations. The assertion is over K, not over the larger E. -/
theorem native_normalized_original_homogeneous_polynomial_zero_iff
    (hL : aeval (R := E) (w) L ≠ 0)
    (P : MvPolynomial (Fin 4) K) {D : ℕ} (hP : P.IsHomogeneous D) :
    aeval (R := K) (fun i => (w) i / aeval (R := E) (w) L) P = 0 ↔ P = 0 := by
  letI : Algebra K E := (ι).toAlgebra
  letI : IsScalarTower K E (N).functionField := IsScalarTower.of_algebraMap_eq' rfl
  rw [← aeval_map_algebra_extension (E := E) P]
  change aeval (R := E) (fun i => (w) i / aeval (R := E) (w) L) (MvPolynomial.map (ι) P) = 0 ↔ P = 0
  have hscale := homogeneous_aeval_scale_indexed (MvPolynomial.map (ι) P) (hP.map (ι))
    (w) (aeval (R := E) (w) L)⁻¹
  have hscale' : aeval (fun i => (w) i / aeval (R := E) (w) L) (MvPolynomial.map (ι) P) =
      (aeval (R := E) (w) L)⁻¹ ^ D * aeval (R := E) (w) (MvPolynomial.map (ι) P) := by
    simpa only [div_eq_mul_inv, mul_comm] using hscale
  rw [hscale', mul_eq_zero, or_iff_right (pow_ne_zero D (inv_ne_zero hL))]
  exact native_original_homogeneous_polynomial_zero_iff H I E hH e P hP

/-- All four original affine source coordinates are algebraically
independent over K after adjoining the independent homogeneous scale. -/
theorem native_independent_scale_original_source_algebraicIndependent
    (hL : aeval (R := E) (w) L ≠ 0) :
    AlgebraicIndependent K (fun i => RatFunc.X * RatFunc.C ((w) i / aeval (R := E) (w) L)) := by
  apply independent_scale_source_algebraicIndependent
  intro P D hP hzero
  exact (native_normalized_original_homogeneous_polynomial_zero_iff H I E hH e L hL P hP).mp hzero

/-- The actual original four-variable rational source field embeds
in the independently scaled native field through its original coordinates. -/
noncomputable def nativeIndependentScaleSourceFieldHom
    (hL : aeval (R := E) (w) L ≠ 0) :
    FractionRing (MvPolynomial (Fin 4) K) →ₐ[K] RatFunc (N).functionField :=
  IsFractionRing.liftAlgHom (algebraicIndependent_iff_injective_aeval.mp
    (native_independent_scale_original_source_algebraicIndependent H I E hH e L hL))

/-- The original source embedding retains every original polynomial,
including the original four output components, without coefficient change. -/
theorem nativeIndependentScaleSourceFieldHom_polynomial
    (hL : aeval (R := E) (w) L ≠ 0) (P : MvPolynomial (Fin 4) K) :
    nativeIndependentScaleSourceFieldHom H I E hH e L hL
      (algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) P) =
      aeval (R := K) (fun i => RatFunc.X * RatFunc.C ((w) i / aeval (R := E) (w) L)) P := by
  unfold nativeIndependentScaleSourceFieldHom
  exact IsFractionRing.lift_algebraMap (algebraicIndependent_iff_injective_aeval.mp
    (native_independent_scale_original_source_algebraicIndependent H I E hH e L hL)) P

/-- Every original source coordinate keeps its own label and the
same independently adjoined homogeneous scale under the actual embedding. -/
theorem nativeIndependentScaleSourceFieldHom_coordinate
    (hL : aeval (R := E) (w) L ≠ 0) (i : Fin 4) :
    nativeIndependentScaleSourceFieldHom H I E hH e L hL (rationalCoordinate (K := K) i) =
      RatFunc.X * RatFunc.C ((w) i / aeval (R := E) (w) L) := by
  change nativeIndependentScaleSourceFieldHom H I E hH e L hL
    (algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) (X i)) = _
  rw [nativeIndependentScaleSourceFieldHom_polynomial, aeval_X]

/-- The source field embedding and the native extended-coefficient
evaluation give exactly the same value of every original polynomial.
This compares the original K(H) values with the constructed target equations. -/
theorem nativeIndependentScaleSourceFieldHom_extended_polynomial
    (hL : aeval (R := E) (w) L ≠ 0) (P : MvPolynomial (Fin 4) K) :
    nativeIndependentScaleSourceFieldHom H I E hH e L hL
      (algebraMap _ (FractionRing (MvPolynomial (Fin 4) K)) P) =
      aeval (R := E) (fun i => RatFunc.X * RatFunc.C ((w) i / aeval (R := E) (w) L))
        (MvPolynomial.map (ι) P) := by
  rw [nativeIndependentScaleSourceFieldHom_polynomial]
  letI : Algebra K E := (ι).toAlgebra
  letI : IsScalarTower K E (RatFunc (N).functionField) := IsScalarTower.of_algebraMap_eq' rfl
  exact (aeval_map_algebra_extension P _).symm

/-- Original ground-field coefficients retain their exact given
closed Gauss coefficient realization under the actual source embedding. -/
theorem nativeIndependentScaleSourceFieldHom_coefficient
    (hL : aeval (R := E) (w) L ≠ 0) (c : K) :
    nativeIndependentScaleSourceFieldHom H I E hH e L hL
      (algebraMap K (FractionRing (MvPolynomial (Fin 4) K)) c) =
      RatFunc.C (algebraMap E (N).functionField ((ι) c)) := by
  exact (nativeIndependentScaleSourceFieldHom H I E hH e L hL).commutes c

end DimensionFourDependence
