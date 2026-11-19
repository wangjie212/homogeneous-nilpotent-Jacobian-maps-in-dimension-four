import DimensionFourDependence.RationalScalarLocalization
import DimensionFourDependence.HomogeneousResidueSpecialization

/-! # Original homogeneous source equations retain the independent scale -/

namespace DimensionFourDependence

open MvPolynomial

variable {E F σ : Type*} [Field E] [Field F] [Algebra E F]

/-- Homogeneous evaluation after adjoining a new source scale keeps
the original value and the exact homogeneous power of the new variable. -/
theorem independent_scale_homogeneous_polynomial_value
    (P : MvPolynomial σ E) {d : ℕ} (hP : P.IsHomogeneous d) (v : σ → F) :
    aeval (fun i => RatFunc.X * RatFunc.C (v i)) P =
      RatFunc.X ^ d * RatFunc.C (aeval v P) := by
  rw [homogeneous_aeval_scale_indexed P hP]
  congr 1
  exact (comp_aeval_apply v (IsScalarTower.toAlgHom E F (RatFunc F)) P).symm

variable {L : Type*} [Field L] [Algebra L F]

/-- An exact original target equation becomes an exact equation over
the enlarged rational coefficient field. Its independent scale is the
new variable, not a scalar chosen in the original field. -/
theorem independent_scale_homogeneous_target_equation
    (γ : RatFunc L →ₐ[L] RatFunc F) (hγ : γ RatFunc.X = RatFunc.X)
    (P : MvPolynomial σ E) {d : ℕ} (hP : P.IsHomogeneous d) (v : σ → F)
    (Y : L) (hY : aeval v P = algebraMap L F Y) :
    aeval (fun i => RatFunc.X * RatFunc.C (v i)) P = γ (RatFunc.X ^ d * RatFunc.C Y) := by
  rw [independent_scale_homogeneous_polynomial_value P hP, hY, map_mul, map_pow, hγ]
  congr 1
  exact ((γ.commutes Y).trans (IsScalarTower.algebraMap_apply L F (RatFunc F) Y)).symm

end DimensionFourDependence
