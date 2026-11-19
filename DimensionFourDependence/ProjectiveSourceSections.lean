import DimensionFourDependence.ProjectiveSourceCoordinates
import DimensionFourDependence.HomogenizeChart
import DimensionFourDependence.HomogeneousEvaluationScaling

/-! # Original homogeneous source sections in actual projective charts

The chart homomorphism sets the selected homogeneous coordinate to one.
On a form of degree d its actual rational source value is P / X_a^d,
the coefficient in the standard regular frame of the hyperplane bundle.
-/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

local notation "R₄" => MvPolynomial (Fin 4) K
local notation "F₄" => FractionRing (MvPolynomial (Fin 4) K)

/-- The polynomial expression of an original source section in the
three free chart coordinates. -/
noncomputable def projectiveSourceDehomogenize (s : Fin 4 ≃ Option (Fin 3)) :
    R₄ →ₐ[K] MvPolynomial (Fin 3) K :=
  projectiveDehomogenize.comp (renameEquiv K s).toAlgHom

/-- The section coefficient in the actual original-coefficient source
chart algebra, with its original ratio-valued coordinates. -/
noncomputable def projectiveSourceSectionHom (s : Fin 4 ≃ Option (Fin 3)) :
    R₄ →ₐ[K] projectiveCoordinateChartAlgebra (C := K)
      (rationalCoordinate (K := K) (n := 4)) (s.symm none) :=
  (projectiveSourceFullChartCoordinateEquiv s).toAlgHom.comp (projectiveSourceDehomogenize s)

/-- Dehomogenizing in a standard source chart cannot increase the
original homogeneous polynomial's total degree. -/
theorem projectiveSourceDehomogenize_totalDegree (s : Fin 4 ≃ Option (Fin 3)) (P : R₄) :
    (projectiveSourceDehomogenize s P).totalDegree ≤ P.totalDegree := by
  exact (projectiveDehomogenize_totalDegree ((renameEquiv K s) P)).trans
    (totalDegree_renameEquiv s P).le

/-- The actual source chart map evaluates every original polynomial at
the original coordinate ratios. -/
theorem projectiveSourceSectionHom_source (s : Fin 4 ≃ Option (Fin 3)) (P : R₄) :
    (projectiveSourceSectionHom s P : F₄) =
      aeval (fun i => rationalCoordinate (K := K) i /
        rationalCoordinate (K := K) (s.symm none)) P := by
  let A := projectiveCoordinateChartAlgebra (C := K)
    (rationalCoordinate (K := K) (n := 4)) (s.symm none)
  have hx : rationalCoordinate (K := K) (s.symm none) ≠ 0 := by
    simpa only [rationalCoordinate, map_zero] using
      (IsFractionRing.injective R₄ F₄).ne (X_ne_zero (s.symm none))
  have hmap : A.val.comp (projectiveSourceSectionHom s) =
      aeval (fun i => rationalCoordinate (K := K) i /
        rationalCoordinate (K := K) (s.symm none)) := by
    apply MvPolynomial.algHom_ext
    intro i
    change (projectiveSourceFullChartCoordinateEquiv (K := K) s
      (projectiveDehomogenize (rename s (X i : R₄))) : F₄) = _
    rw [projectiveSourceFullChartCoordinateEquiv_source, rename_X, aeval_X]
    rcases hsi : s i with _ | j
    · have hi : i = s.symm none := by rw [← hsi, s.symm_apply_apply]
      simp only [projectiveDehomogenize_X_none, map_one]
      rw [hi, div_self hx]
    · simp only [projectiveDehomogenize_X_some, aeval_X]
      change rationalCoordinate (K := K) (s.symm (some j)) /
        rationalCoordinate (K := K) (s.symm none) = _
      rw [← hsi, s.symm_apply_apply]
  exact DFunLike.congr_fun hmap P

/-- A degree-d original homogeneous source form has actual chart
coefficient P / X_a^d in the standard local section frame. -/
theorem projectiveSourceSectionHom_homogeneous_value
    (s : Fin 4 ≃ Option (Fin 3)) (P : R₄) {d : ℕ} (hP : P.IsHomogeneous d) :
    (projectiveSourceSectionHom s P : F₄) =
      algebraMap R₄ F₄ P / rationalCoordinate (K := K) (s.symm none) ^ d := by
  rw [projectiveSourceSectionHom_source]
  have he := homogeneous_aeval_scale P hP (rationalCoordinate (K := K))
    (rationalCoordinate (K := K) (s.symm none))⁻¹
  have hpoint :
      (fun i => (rationalCoordinate (K := K) (s.symm none))⁻¹ * rationalCoordinate (K := K) i) =
        (fun i => rationalCoordinate (K := K) i / rationalCoordinate (K := K) (s.symm none)) := by
    funext i
    rw [div_eq_mul_inv, mul_comm]
  rw [hpoint] at he
  rw [he]
  have hmap : (aeval (rationalCoordinate (K := K)) : R₄ →ₐ[K] F₄) =
      IsScalarTower.toAlgHom K R₄ F₄ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [rationalCoordinate]
  rw [hmap, div_eq_mul_inv, inv_pow, mul_comm]
  rfl

end DimensionFourDependence
