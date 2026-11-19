import DimensionFourDependence.RulingScalarExtensionDensity
import DimensionFourDependence.ActualGaussRulingDensity
import DimensionFourDependence.PrimitiveBoundaryParameter

/-! # The original Gauss parameter is constant on the actual ruling

A homogeneous quotient for the original birational Gauss parameter
gives a polynomial relation over the actual Gauss field at the original
output. Actual ruling density transports this relation to every field
extension. At a projectively generic point the homogeneous denominator
is nonzero, so the parameter value is the original target parameter.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d)
    (hrank : polyRank (jac H) = 3) (I : ImageRelationWitness H)
    (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "M" => projectiveRatioField (K := K)
  (rationalImageNormal H I.equation) (imageNormalPivot H I)
local notation "Q" => fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)

include hd hH hrank hGauss

/-- The original cone parameter quotient yields its exact homogeneous
cross relation at every extension-field point of the actual ruling. -/
theorem actual_gauss_ruling_original_parameter_cross_relation
    (hA : Module.finrank (M) (LinearMap.ker (actualGaussRulingMatrix H I e).toLin') = 2)
    (r s : MvPolynomial (Fin 4) K)
    (hscone : algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField s ≠ 0)
    (ht : imageConeGaussHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField r /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField s)
    (κ : Type u) [Field κ] [Algebra (M) κ] [Algebra K κ] [IsScalarTower K (M) κ]
    (b : Fin 4 → κ)
    (hb : (actualGaussRulingMatrix H I e).map (algebraMap (M) κ) *ᵥ b = 0) :
    aeval b r = algebraMap (M) κ (e RatFunc.X) * aeval b s := by
  have hsQ : aeval (Q) s ≠ 0 := by
    have hh := (imageConeResidueEmbedding H).injective.ne hscone
    change imageConeResidueEmbedding H
      (algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField s) ≠
        imageConeResidueEmbedding H 0 at hh
    rw [map_zero, imageConeResidueEmbedding_polynomial, aeval_polynomial_to_fraction] at hh
    exact hh
  have hrep := congrArg (imageConeResidueEmbedding H) ht
  rw [imageConeGaussHom_realization, map_div₀,
    imageConeResidueEmbedding_polynomial, imageConeResidueEmbedding_polynomial,
    aeval_polynomial_to_fraction, aeval_polynomial_to_fraction] at hrep
  let T : MvPolynomial (Fin 4) (M) :=
    MvPolynomial.map (algebraMap K (M)) r - C (e RatFunc.X) * MvPolynomial.map (algebraMap K (M)) s
  have hT : aeval (Q) T = 0 := by
    simp only [T, map_sub, map_mul, aeval_C, aeval_map_algebra_extension]
    change aeval (Q) r - gaussParameterSourceHom H I e RatFunc.X * aeval (Q) s = 0
    exact sub_eq_zero.mpr ((eq_div_iff hsQ).mp hrep).symm
  have he := two_dimensional_matrix_kernel_generic_point_density_extension
    (actualGaussRulingMatrix H I e) hA (Q) (I.output_mem_actual_gauss_ruling H hd hH e)
    (actual_gauss_fiber_output_trdeg_two H hrank I hGauss) T hT b hb
  simp only [T, map_sub, map_mul, aeval_C, aeval_map_algebra_extension] at he
  exact sub_eq_zero.mp he

/-- Wherever a homogeneous presentation of the original parameter
has nonzero denominator, its value on the actual ruling is the target
parameter itself, also over arbitrary extension fields. -/
theorem actual_gauss_ruling_original_parameter_value
    (hA : Module.finrank (M) (LinearMap.ker (actualGaussRulingMatrix H I e).toLin') = 2)
    (r s : MvPolynomial (Fin 4) K)
    (hscone : algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField s ≠ 0)
    (ht : imageConeGaussHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField r /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField s)
    (κ : Type u) [Field κ] [Algebra (M) κ] [Algebra K κ] [IsScalarTower K (M) κ]
    (b : Fin 4 → κ)
    (hb : (actualGaussRulingMatrix H I e).map (algebraMap (M) κ) *ᵥ b = 0)
    (hsb : aeval b s ≠ 0) :
    aeval b r / aeval b s = algebraMap (M) κ (e RatFunc.X) := by
  apply (div_eq_iff hsb).mpr
  exact actual_gauss_ruling_original_parameter_cross_relation H hd hH hrank I hGauss e hA
    r s hscone ht κ b hb

/-- A projectively generic point of the original image lying on the
actual ruling has the target's original birational Gauss parameter.
The denominator's nonvanishing is derived from projective genericity. -/
theorem projective_generic_actual_gauss_ruling_original_parameter_value
    (hH0 : H ≠ 0)
    (hA : Module.finrank (M) (LinearMap.ker (actualGaussRulingMatrix H I e).toLin') = 2)
    (r s : MvPolynomial (Fin 4) K) {m : ℕ} (hs : s.IsHomogeneous m)
    (hscone : algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField s ≠ 0)
    (ht : imageConeGaussHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField r /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField s)
    (κ : Type u) [Field κ] [Algebra (M) κ] [Algebra K κ] [IsScalarTower K (M) κ]
    (b : Fin 4 → κ) (hb0 : b ≠ 0)
    (hbgen : projectiveFieldPoint (E := K) b hb0 = projectiveImageGenericPoint H hd hH hH0)
    (hb : (actualGaussRulingMatrix H I e).map (algebraMap (M) κ) *ᵥ b = 0) :
    aeval b r / aeval b s = algebraMap (M) κ (e RatFunc.X) :=
  actual_gauss_ruling_original_parameter_value H hd hH hrank I hGauss e hA r s hscone ht κ b hb
    (projective_generic_homogeneous_denominator_ne_zero H hd hH hH0 b hb0 hbgen s hs hscone)

end DimensionFourDependence
