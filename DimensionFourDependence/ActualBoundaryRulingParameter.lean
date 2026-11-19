import DimensionFourDependence.ActualBoundaryDirectionDominance
import DimensionFourDependence.ActualRulingGaussParameter

/-! # Comparing original Gauss parameters in actual boundary residue fields

The actual Gauss field embeds in the actual graph coefficient field
because it already lies in the original output field. This fixes its
embedding in every actual boundary residue field. Ruling density then
compares the original parameter quotient at a generic boundary direction
with its value at the actual target.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

attribute [local instance] coefficientFieldScalarTower

universe u

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option quotPrecheck false

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (hrank : polyRank (jac H) = 3)
    (p : Equiv.Perm (Fin 4))
    (hY : AlgebraicIndependent K (fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K)
      (FractionRing (MvPolynomial (Fin 4) K)) (H (p i.castSucc))))

local notation "S₀" => FractionRing (MvPolynomial (Fin 4) K)
local notation "Y" => fun i : Fin 3 => algebraMap (MvPolynomial (Fin 4) K) S₀ (H (p i.castSucc))
local notation "L" => coefficientField (K := K) (Y)
local notation "y₀" => actualChartOutputCoordinate H hrank p hY

include hY hrank

/-- The original Gauss field lies in the actual chart coefficient
field directly through the original output field. -/
theorem actual_gauss_field_le_actual_chart_coefficient_field (I : ImageRelationWitness H) :
    projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I) ≤
      (L).restrictScalars K := by
  intro z hz
  exact fullOutputField_mem_coefficientField
    (fun j => algebraMap (MvPolynomial (Fin 4) K) S₀ (H j))
    (by rw [rationalJacobian_polynomial H]; exact hrank) p hY
    ⟨z, actual_gauss_field_le_output_field H I hz⟩

/-- The actual original Gauss field with its original-source
realization, embedded in the actual graph coefficient field. -/
noncomputable def actualChartGaussFieldHom (I : ImageRelationWitness H) :
    projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I) →ₐ[K] (L) :=
  IntermediateField.inclusion (actual_gauss_field_le_actual_chart_coefficient_field H hrank p hY I)

/-- Evaluating a polynomial at the actual output constants retains
its exact original-source value. -/
theorem actualChartOutputCoordinate_source_evaluation (R : MvPolynomial (Fin 4) K) :
    algebraMap (L) S₀ (aeval (y₀) R) =
      aeval (fun i => algebraMap (MvPolynomial (Fin 4) K) S₀ (H i)) R := by
  change (IsScalarTower.toAlgHom K (L) S₀) (aeval (y₀) R) = _
  rw [comp_aeval_apply (y₀) (IsScalarTower.toAlgHom K (L) S₀) R]
  change aeval (fun i => algebraMap (L) S₀ ((y₀) i)) R = _
  rw [funext (actualChartOutputCoordinate_source H hrank p hY)]

/-- The original cone's parameter quotient at every actual extended
target is the original Gauss-field parameter in that same extension. -/
theorem actual_target_original_gauss_parameter_value
    (I : ImageRelationWitness H)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (r s : MvPolynomial (Fin 4) K)
    (ht : imageConeGaussHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField r /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField s)
    (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ] [IsScalarTower K (L) κ] :
    aeval (fun i => algebraMap (L) κ ((y₀) i)) r /
        aeval (fun i => algebraMap (L) κ ((y₀) i)) s =
      algebraMap (L) κ (actualChartGaussFieldHom H hrank p hY I (e RatFunc.X)) := by
  have heL : aeval (y₀) r / aeval (y₀) s =
      actualChartGaussFieldHom H hrank p hY I (e RatFunc.X) := by
    apply (algebraMap (L) S₀).injective
    change algebraMap (L) S₀ (_ / _) = algebraMap (L) S₀ _
    rw [map_div₀, actualChartOutputCoordinate_source_evaluation,
      actualChartOutputCoordinate_source_evaluation]
    have he := congrArg (imageConeResidueEmbedding H) ht
    rw [imageConeGaussHom_realization, map_div₀,
      imageConeResidueEmbedding_polynomial, imageConeResidueEmbedding_polynomial,
      aeval_polynomial_to_fraction, aeval_polynomial_to_fraction] at he
    exact he.symm
  have heκ := congrArg (algebraMap (L) κ) heL
  rw [map_div₀] at heκ
  change (IsScalarTower.toAlgHom K (L) κ) (aeval (y₀) r) /
    (IsScalarTower.toAlgHom K (L) κ) (aeval (y₀) s) = _ at heκ
  rw [comp_aeval_apply (y₀) (IsScalarTower.toAlgHom K (L) κ) r,
    comp_aeval_apply (y₀) (IsScalarTower.toAlgHom K (L) κ) s] at heκ
  exact heκ

/-- For a generic actual boundary direction on the actual ruling,
the original Gauss-parameter quotient has exactly its actual target's
value. The coefficient embeddings and parameter comparison are derived. -/
theorem actual_boundary_original_parameter_comparison_of_ruling
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hH0 : H ≠ 0)
    (I : ImageRelationWitness H) (hGauss : gaussImageDimension H I = 1)
    (e : RatFunc K ≃ₐ[K] projectiveRatioField (K := K)
      (rationalImageNormal H I.equation) (imageNormalPivot H I))
    (hA : Module.finrank
      (projectiveRatioField (K := K) (rationalImageNormal H I.equation) (imageNormalPivot H I))
      (LinearMap.ker (actualGaussRulingMatrix H I e).toLin') = 2)
    (r s : MvPolynomial (Fin 4) K) {m : ℕ} (hs : s.IsHomogeneous m)
    (hscone : algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField s ≠ 0)
    (ht : imageConeGaussHom H I e RatFunc.X =
      algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField r /
        algebraMap (MvPolynomial (Fin 4) K) (imageRelationIdeal H).ResidueField s)
    (κ : Type u) [Field κ] [Algebra (L) κ] [Algebra K κ] [IsScalarTower K (L) κ]
    (b : Fin 4 → κ) (hb0 : b ≠ 0)
    (hbgen : projectiveFieldPoint (E := K) b hb0 = projectiveImageGenericPoint H hd hH hH0)
    (hb : (actualGaussRulingMatrix H I e).map
      ((algebraMap (L) κ).comp (actualChartGaussFieldHom H hrank p hY I).toRingHom) *ᵥ b = 0) :
    aeval b r / aeval b s =
      aeval (fun i => algebraMap (L) κ ((y₀) i)) r /
        aeval (fun i => algebraMap (L) κ ((y₀) i)) s := by
  let M := projectiveRatioField (K := K)
    (rationalImageNormal H I.equation) (imageNormalPivot H I)
  let f : M →ₐ[K] κ :=
    (IsScalarTower.toAlgHom K (L) κ).comp (actualChartGaussFieldHom H hrank p hY I)
  let : Algebra M κ := f.toRingHom.toAlgebra
  let : IsScalarTower K M κ := IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  have he := projective_generic_actual_gauss_ruling_original_parameter_value
    H hd hH hrank I hGauss e hH0 hA r s hs hscone ht κ b hb0 hbgen hb
  exact he.trans (actual_target_original_gauss_parameter_value H hrank p hY I e r s ht κ).symm

end DimensionFourDependence
