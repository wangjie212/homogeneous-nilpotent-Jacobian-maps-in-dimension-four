import DimensionFourDependence.GraphLineChart

/-! # Coordinate pivots for projective-line charts

Independent vectors have a nonzero two-by-two coordinate minor. Two
distinct pivot coordinates can be placed first by a permutation. These
facts will give coverage of all projective lines by the matrix charts.
-/

namespace DimensionFourDependence

open Matrix

variable {F : Type*} [Field F]

/-- Independent vectors have a nonzero two-by-two coordinate minor. -/
theorem independent_pair_exists_nonzero_coordinate_minor {n : ℕ}
    (u v : Fin n → F) (hli : LinearIndependent F ![u, v]) :
    ∃ i j, u i * v j - u j * v i ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hv : v ≠ 0 := by simpa using hli.ne_zero 1
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hv
  have he : u = (u i / v i) • v := by
    funext j
    change u j = (u i / v i) * v j
    apply mul_right_cancel₀ hi
    calc
      u j * v i = u i * v j := (sub_eq_zero.mp (hnone i j)).symm
      _ = (u i / v i * v j) * v i := by field_simp
  exact (linearIndependent_fin2.mp hli).2 (u i / v i) he.symm

/-- A nonzero two-by-two determinant gives independence of its column vectors. -/
theorem independent_pair_of_coordinate_minor (a b c d : F) (hdet : a * d - c * b ≠ 0) :
    LinearIndependent F ![![a, c], ![b, d]] := by
  rw [LinearIndependent.pair_iff]
  intro r s h
  have h0 : r * a + s * b = 0 := by simpa using congrFun h 0
  have h1 : r * c + s * d = 0 := by simpa using congrFun h 1
  have hr : r * (a * d - c * b) = 0 := by linear_combination d * h0 - b * h1
  have hs : s * (a * d - c * b) = 0 := by linear_combination a * h1 - c * h0
  exact ⟨(mul_eq_zero.mp hr).resolve_right hdet, (mul_eq_zero.mp hs).resolve_right hdet⟩

/-- Any two distinct coordinates can be placed first by a permutation. -/
theorem exists_permutation_first_two (i j : Fin 4) (hij : i ≠ j) :
    ∃ p : Equiv.Perm (Fin 4), p 0 = i ∧ p 1 = j := by
  let e : Equiv.Perm (Fin 4) := Equiv.swap 0 i
  let k := e.symm j
  have hk : k ≠ 0 := by
    intro hz
    have hji : j = i := by
      calc
        j = e k := by simp [k]
        _ = e 0 := by rw [hz]
        _ = i := by simp [e]
    exact hij hji.symm
  refine ⟨(Equiv.swap 1 k).trans e, ?_, ?_⟩
  · have hs : Equiv.swap 1 k (0 : Fin 4) = 0 := by
      simp [Equiv.swap_apply_def, hk.symm]
    change e (Equiv.swap 1 k 0) = i
    rw [hs]
    simp [e]
  · change e (Equiv.swap 1 k 1) = j
    simp [k]

/-- Permute the four vector coordinates, with the selected pivots first. -/
def lineCoordinatePermutation (p : Equiv.Perm (Fin 4)) : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) where
  toFun x := x ∘ p
  invFun x := x ∘ p.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The pivot projection used by the graph chart. -/
def linePivotProjection (p : Equiv.Perm (Fin 4)) : (Fin 4 → F) →ₗ[F] (Fin 2 → F) where
  toFun x := ![x (p 0), x (p 1)]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

end DimensionFourDependence
