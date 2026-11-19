import DimensionFourDependence.DependentTernaryChartPlanarConjugacy
import DimensionFourDependence.HomogeneousMatrixBlockNilpotence
import DimensionFourDependence.PlanarActiveNormalization

/-! # Nilpotence of the homogeneous core and its leading planar block -/

namespace DimensionFourDependence

open MvPolynomial Matrix

variable {K : Type*} [Field K]
local notation "R₄" => MvPolynomial (Fin 4) K

theorem normalizedFixedCoordinateHomogeneousCore_nilpotent
    (B : Fin 3 → R₄) {d : ℕ} (hB : ∀ i, (B i).IsHomogeneous d)
    (hN : IsNilpotent (jac (normalizedFixedCoordinateChart B))) :
    IsNilpotent (jac (normalizedFixedCoordinateHomogeneousCore B d)) := by
  let G := normalizedFixedCoordinateHomogeneousCore B d
  let M := jac G
  let W := M.submatrix Fin.castSucc Fin.castSucc
  have hG : IsHomogMap G d := normalizedFixedCoordinateHomogeneousCore_isHomogMap B hB
  have hz (j : Fin 4) : M (Fin.last 3) j = 0 := by
    simp only [M, G, jac, Matrix.of_apply, normalizedFixedCoordinateHomogeneousCore,
      Fin.lastCases_last, map_zero]
  have hmap : W.map (lastCoordinateDehomogenize (K := K) (n := 3)) =
      jac (normalizedFixedCoordinateChart B) := by
    let B' : Fin 3 → R₄ := fun i => lastCoordinateHomogenize (normalizedFixedCoordinateChart B i) d
    change ((jac (Fin.lastCases 0 B')).submatrix Fin.castSucc Fin.castSucc).map
      (lastCoordinateDehomogenize (K := K) (n := 3)) = _
    rw [← lastCoordinateDehomogenize_leading_jacobian B']
    simp only [B', lastCoordinateDehomogenize_homogenize]
  have hhom (i j : Fin 3) : (W i j).IsHomogeneous (d - 1) := by
    change (pderiv j.castSucc (G i.castSucc)).IsHomogeneous (d - 1)
    exact (hG i.castSucc).pderiv
  obtain ⟨k, hk⟩ : IsNilpotent (W.map (lastCoordinateDehomogenize (K := K) (n := 3))) :=
    hmap.symm ▸ hN
  have hk' : W ^ k = 0 := homogeneous_matrix_pow_zero_of_dehomogenize_pow_zero W hhom hk
  have hpos : 0 < k := by
    by_contra! hn
    rw [Nat.eq_zero_of_le_zero hn, pow_zero] at hk'
    exact one_ne_zero hk'
  exact ⟨k + 1, block_pow_succ_zero_of_leading_block_pow_zero M hz hpos hk'⟩

/-- The actual nilpotent Jacobian with its two fixed final coordinates
has a nilpotent leading active block over the original polynomial ring. -/
theorem planarActiveJacobian_nilpotent_of_full_nilpotent
    (A : Fin 2 → R₄) (hN : IsNilpotent (jac (![A 0, A 1, 0, 0] : Fin 4 → R₄))) :
    IsNilpotent (Shear.planarActiveJacobian A) := by
  let H : Fin 4 → R₄ := ![A 0, A 1, 0, 0]
  let M : Matrix (Fin 3) (Fin 3) R₄ := (jac H).submatrix Fin.castSucc Fin.castSucc
  have hM : IsNilpotent M := leading_jacobian_isNilpotent_of_last_component_zero H hN rfl
  have hz (j : Fin 3) : M (Fin.last 2) j = 0 := by
    change pderiv j.castSucc (0 : R₄) = 0
    exact map_zero _
  have he : M.submatrix Fin.castSucc Fin.castSucc = Shear.planarActiveJacobian A := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [← he]
  exact leading_block_isNilpotent_of_last_row_zero M hM hz

end DimensionFourDependence
