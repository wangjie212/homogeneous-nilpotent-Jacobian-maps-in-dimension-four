import DimensionFourDependence.ShearJacobian
import DimensionFourDependence.LinearTameConjugacy

/-! # A binary base coordinate change with the active sign change of Lemma 6.2 -/

namespace DimensionFourDependence.Shear

open Matrix MvPolynomial

set_option maxHeartbeats 2200000

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "M₂" => Matrix (Fin 2) (Fin 2) K

theorem base4_eq_rename (p : R₂) : base4 p = rename (Fin.natAdd 2) p := by
  have he : (aeval (![X 2, X 3] : Fin 2 → R₄)) = rename (Fin.natAdd 2) := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;> simp
  exact AlgHom.congr_fun he p

/-- Substitution by `(x,-y,A(z,t),B(z,t))`, where the last two
coordinate forms are the rows of the actual constant matrix. -/
noncomputable def signBaseFrameHom4 (T : M₂) : R₄ →ₐ[K] R₄ :=
  aeval ![X 0, -X 1, base4 (linearPolynomialMap T 0), base4 (linearPolynomialMap T 1)]

theorem signBaseFrameHom4_X (T : M₂) (j : Fin 4) :
    signBaseFrameHom4 T (X j) =
      ![X 0, -X 1, base4 (linearPolynomialMap T 0), base4 (linearPolynomialMap T 1)] j := by
  simp [signBaseFrameHom4]

theorem signBaseFrameHom4_base (T : M₂) (p : R₂) :
    signBaseFrameHom4 T (base4 p) = base4 (linearPolynomialPullback T p) := by
  unfold base4 linearPolynomialPullback
  rw [Tame.algHom_aeval, comp_aeval_apply]
  congr 1
  have he : (fun i : Fin 2 => (signBaseFrameHom4 T) ((![X 2, X 3] : Fin 2 → R₄) i)) =
      (fun i : Fin 2 => (aeval (![X 2, X 3] : Fin 2 → R₄)) (linearPolynomialMap T i)) := by
    funext i
    fin_cases i <;> simp [signBaseFrameHom4_X, base4]
  rw [he]

theorem signBaseFrameHom4_comp_inverse (T S : M₂) (h : S * T = 1) :
    (signBaseFrameHom4 T).comp (signBaseFrameHom4 S) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro j
  have hbase (i : Fin 2) : signBaseFrameHom4 T (base4 (linearPolynomialMap S i)) =
      base4 (X i) := by
    rw [signBaseFrameHom4_base]
    have hcomp := matrix_linear_polynomial_substitution_inverse S T h (X i)
    simp only [linearPolynomialPullback, aeval_X] at hcomp
    rw [show linearPolynomialPullback T (linearPolynomialMap S i) = X i from hcomp]
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  rw [signBaseFrameHom4_X]
  fin_cases j
  · simp [signBaseFrameHom4_X]
  · simp [signBaseFrameHom4_X]
  · change signBaseFrameHom4 T (base4 (linearPolynomialMap S 0)) = X 2
    rw [hbase]
    simp [base4]
  · change signBaseFrameHom4 T (base4 (linearPolynomialMap S 1)) = X 3
    rw [hbase]
    simp [base4]

/-- A nonsingular binary base change lifts to an actual invertible
linear change of all four coordinates, with the second active variable negated. -/
noncomputable def signBaseFrameEquiv4 (T : M₂) (h : IsUnit T.det) : R₄ ≃ₐ[K] R₄ :=
  AlgEquiv.ofAlgHom (signBaseFrameHom4 T) (signBaseFrameHom4 T⁻¹)
    (signBaseFrameHom4_comp_inverse _ _ (Matrix.nonsing_inv_mul T h))
    (signBaseFrameHom4_comp_inverse _ _ (Matrix.mul_nonsing_inv T h))

theorem signBaseFrameEquiv4_X (T : M₂) (h : IsUnit T.det) (j : Fin 4) :
    signBaseFrameEquiv4 T h (X j) =
      ![X 0, -X 1, base4 (linearPolynomialMap T 0), base4 (linearPolynomialMap T 1)] j :=
  signBaseFrameHom4_X T j

theorem signBaseFrameEquiv4_base (T : M₂) (h : IsUnit T.det) (p : R₂) :
    signBaseFrameEquiv4 T h (base4 p) = base4 (linearPolynomialPullback T p) :=
  signBaseFrameHom4_base T p

theorem signBaseFrameEquiv4_isAffine (T : M₂) (h : IsUnit T.det) :
    Tame.IsAffine (signBaseFrameEquiv4 T h) := by
  have hb (i : Fin 2) : (base4 (linearPolynomialMap T i)).totalDegree ≤ 1 := by
    have hh : (base4 (linearPolynomialMap T i)).IsHomogeneous 1 := by
      rw [base4_eq_rename]
      exact (linearPolynomialMap_homogeneous T i).rename_isHomogeneous
    by_cases hz : base4 (linearPolynomialMap T i) = 0
    · simp [hz]
    · exact (hh.totalDegree hz).le
  intro j
  rw [signBaseFrameEquiv4_X]
  fin_cases j <;> simp [hb]

end DimensionFourDependence.Shear
