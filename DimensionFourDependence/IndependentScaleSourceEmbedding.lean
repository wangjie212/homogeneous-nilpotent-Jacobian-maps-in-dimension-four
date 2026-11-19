import DimensionFourDependence.IndependentScaleHomogeneousValues
import DimensionFourDependence.ExtensionFieldProjectivePoint
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin

/-! # Independent homogeneous scaling reconstructs the original source field -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K F σ : Type*} [Field K] [Field F] [Algebra K F]

/-- Grading by the new independent scale retains every homogeneous
component of an arbitrary original source polynomial. -/
theorem independent_scale_source_polynomial_value (v : σ → F) (P : MvPolynomial σ K) :
    aeval (fun i => RatFunc.X * RatFunc.C (v i)) P =
      algebraMap (Polynomial F) (RatFunc F) (projectiveFieldPointMap (E := K) v P) := by
  have he : aeval (R := K) (fun i => RatFunc.X * RatFunc.C (v i)) =
      (IsScalarTower.toAlgHom K (Polynomial F) (RatFunc F)).comp
        (projectiveFieldPointMap (E := K) v) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [aeval_X, AlgHom.comp_apply]
    change RatFunc.X * RatFunc.C (v i) =
      algebraMap (Polynomial F) (RatFunc F) (projectiveFieldPointMap (E := K) v (X i))
    rw [projectiveFieldPointMap_homogeneous v (isHomogeneous_X _ _), aeval_X,
      RatFunc.algebraMap_monomial, pow_one]
    exact mul_comm _ _
  exact DFunLike.congr_fun he P

/-- Absence of original homogeneous relations implies algebraic
independence of all original source coordinates after adjoining one
free scale. Arbitrary nonhomogeneous relations are separated by degree. -/
theorem independent_scale_source_algebraicIndependent (v : σ → F)
    (hhom : ∀ (P : MvPolynomial σ K) (d : ℕ), P.IsHomogeneous d → aeval v P = 0 → P = 0) :
    AlgebraicIndependent K (fun i => RatFunc.X * RatFunc.C (v i)) := by
  apply algebraicIndependent_iff.mpr
  intro P hP
  have hgraded : projectiveFieldPointMap (E := K) v P = 0 := by
    apply IsFractionRing.injective (Polynomial F) (RatFunc F)
    rw [← independent_scale_source_polynomial_value v P, hP, map_zero]
  have hc (d : ℕ) : homogeneousComponent d P = 0 := by
    apply hhom _ d (homogeneousComponent_isHomogeneous d P)
    rw [← projectiveFieldPointMap_coeff v P d, hgraded, Polynomial.coeff_zero]
  rw [← sum_homogeneousComponent P]
  simp only [hc, Finset.sum_const_zero]

/-- The actual original rational source field embeds by its original
coordinate values in the independently scaled native field. -/
noncomputable def independentScaleSourceFieldHom (v : σ → F)
    (hhom : ∀ (P : MvPolynomial σ K) (d : ℕ), P.IsHomogeneous d → aeval v P = 0 → P = 0) :
    FractionRing (MvPolynomial σ K) →ₐ[K] RatFunc F :=
  IsFractionRing.liftAlgHom
    (algebraicIndependent_iff_injective_aeval.mp (independent_scale_source_algebraicIndependent v hhom))

/-- Every original polynomial has its exact original scaled source
value under the constructed source fraction-field embedding. -/
theorem independentScaleSourceFieldHom_polynomial (v : σ → F)
    (hhom : ∀ (P : MvPolynomial σ K) (d : ℕ), P.IsHomogeneous d → aeval v P = 0 → P = 0)
    (P : MvPolynomial σ K) :
    independentScaleSourceFieldHom v hhom (algebraMap _ (FractionRing (MvPolynomial σ K)) P) =
      aeval (fun i => RatFunc.X * RatFunc.C (v i)) P := by
  unfold independentScaleSourceFieldHom
  exact IsFractionRing.lift_algebraMap
    (algebraicIndependent_iff_injective_aeval.mp (independent_scale_source_algebraicIndependent v hhom)) P

end DimensionFourDependence
