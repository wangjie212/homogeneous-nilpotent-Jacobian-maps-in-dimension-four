import DimensionFourDependence.PlanarActiveNormalization
import DimensionFourDependence.HomogeneousEvaluationScaling

/-! # Specializing the unused fourth variable of a planar lift -/

namespace DimensionFourDependence

open MvPolynomial

variable {K : Type*} [Field K]

noncomputable def lastCoordinateAtZero {n : ℕ} :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (Fin.lastCases 0 X)

theorem lastCoordinateAtZero_X_castSucc {n : ℕ} (i : Fin n) :
    lastCoordinateAtZero (X i.castSucc : MvPolynomial (Fin (n + 1)) K) = X i := by
  simp only [lastCoordinateAtZero, aeval_X, Fin.lastCases_castSucc]

theorem lastCoordinateAtZero_X_last {n : ℕ} :
    lastCoordinateAtZero (X (Fin.last n) : MvPolynomial (Fin (n + 1)) K) = 0 := by
  simp only [lastCoordinateAtZero, aeval_X, Fin.lastCases_last]

theorem lastCoordinateAtZero_rename {n : ℕ} (p : MvPolynomial (Fin n) K) :
    lastCoordinateAtZero (rename Fin.castSucc p) = p := by
  have e : (lastCoordinateAtZero (K := K) (n := n)).comp (rename Fin.castSucc) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, rename_X, lastCoordinateAtZero_X_castSucc]
  exact AlgHom.congr_fun e p

local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "D" => (lastCoordinateAtZero (K := K) (n := 3))
local notation "z" => (X 2 : R₃)

/-- A homogeneous form on any constant direction restricts to a single
power, with its original scalar value as the coefficient. -/
theorem homogeneous_aeval_scaled_scalar_point {n : ℕ} (p : MvPolynomial (Fin n) K) {d : ℕ}
    (hp : p.IsHomogeneous d) (u : Fin n → K) (r : R₃) :
    aeval (fun j => r * C (u j)) p = C (aeval u p) * r ^ d := by
  rw [homogeneous_aeval_scale p hp]
  have he : (Algebra.ofId K R₃).comp (aeval u) = aeval (fun j => C (u j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, aeval_X, Algebra.ofId_apply, algebraMap_eq]
  have h := AlgHom.congr_fun he p
  change C (aeval u p) = aeval (fun j => C (u j)) p at h
  rw [← h, mul_comm]

theorem lastCoordinateAtZero_base4_homogeneous (a : R₂) {r : ℕ}
    (ha : a.IsHomogeneous r) :
    D (Shear.base4 a) = C (aeval (![1, 0] : Fin 2 → K) a) * z ^ r := by
  change D (aeval (![X 2, X 3] : Fin 2 → R₄) a) = _
  rw [Tame.algHom_aeval]
  have h : (fun i : Fin 2 => D (![X 2, X 3] i)) = fun i => z * C (![1, 0] i : K) := by
    funext i
    fin_cases i
    · change D (X (Fin.last 2).castSucc) = z * C 1
      rw [lastCoordinateAtZero_X_castSucc, map_one, mul_one]
      rfl
    · change D (X (Fin.last 3)) = z * C 0
      rw [lastCoordinateAtZero_X_last, map_zero, mul_zero]
  rw [h]
  exact homogeneous_aeval_scaled_scalar_point a ha ![1, 0] z

/-- The original active origin value of a ternary polynomial. -/
noncomputable def ternaryPlanarScalar (p : R₃) : K := aeval (![0, 0, 1] : Fin 3 → K) p

noncomputable def ternaryPlanarNormalized (p : R₃) (d : ℕ) : R₃ :=
  p - C (ternaryPlanarScalar p) * z ^ d

theorem lastCoordinateAtZero_normalized_planar_lift (p : R₃) {d : ℕ}
    (hp : p.IsHomogeneous d) :
    D (Shear.planarActiveNormalized (rename Fin.castSucc p)) = ternaryPlanarNormalized p d := by
  rw [Shear.planarActiveNormalized, map_sub, lastCoordinateAtZero_rename,
    Shear.base4_planarActiveConstant, Tame.algHom_aeval, aeval_rename]
  have h : (fun i : Fin 3 => D ((![0, 0, X 2, X 3] : Fin 4 → R₄) i.castSucc)) =
      fun i => z * C (![0, 0, 1] i : K) := by
    funext i
    fin_cases i
    · change D (0 : R₄) = z * C 0
      simp
    · change D (0 : R₄) = z * C 0
      simp
    · change D (X (Fin.last 2).castSucc) = z * C 1
      rw [lastCoordinateAtZero_X_castSucc, map_one, mul_one]
      rfl
  change p - aeval (fun i : Fin 3 => D ((![0, 0, X 2, X 3] : Fin 4 → R₄) i.castSucc)) p =
    ternaryPlanarNormalized p d
  rw [h, homogeneous_aeval_scaled_scalar_point p hp]
  rfl

end DimensionFourDependence
