import DimensionFourDependence.IsotropicQuadraticBaseChange

/-! # The orthogonal plane of an isotropic direction for a rank-two Hessian

In three dimensions a radial radical and a nonradial isotropic vector
span its orthogonal plane. This is the linear algebra in Section 3.2.
-/

namespace DimensionFourDependence

open Matrix Module

variable {F : Type*} [Field F] {n : ℕ}

theorem matrixBilinearPairing_eq_dot_mulVec (T : Matrix (Fin n) (Fin n) F) (x y : Fin n → F) :
    matrixBilinearPairing T x y = x ⬝ᵥ (T *ᵥ y) := by
  simp only [matrixBilinearPairing, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The rank-two Hessian makes the orthogonal space of an isotropic
nonradial direction exactly the plane spanned by it and the radial vector. -/
theorem rank_two_isotropic_orthogonal_plane
    (T : Matrix (Fin 3) (Fin 3) F) (hT : ∀ i j, T i j = T j i) (hrank : T.rank = 2)
    (Y Z : Fin 3 → F) (hYZ : LinearIndependent F ![Y, Z])
    (hY : T *ᵥ Y = 0) (hZ : matrixBilinearPairing T Z Z = 0)
    (w : Fin 3 → F) (hw : matrixBilinearPairing T w Z = 0) :
    w ∈ Submodule.span F (Set.range ![Y, Z]) := by
  classical
  let U := Submodule.span F (Set.range ![Y, Z])
  have hdimU : finrank F U = 2 := by simpa [U] using finrank_span_eq_card hYZ
  have hdimT := LinearMap.finrank_range_add_finrank_ker T.toLin'
  have hrT : finrank F (LinearMap.range T.toLin') = 2 := hrank
  simp only [Module.finrank_pi, Fintype.card_fin] at hdimT
  have hkT : finrank F (LinearMap.ker T.toLin') = 1 := by omega
  have hTZ : T *ᵥ Z ≠ 0 := by
    intro hz
    have hle : U ≤ LinearMap.ker T.toLin' := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> assumption
    have hb := Submodule.finrank_mono hle
    omega
  let f := (dotProductBilin F F) (T *ᵥ Z)
  have hf (v : Fin 3 → F) : f v = matrixBilinearPairing T v Z := by
    change (T *ᵥ Z) ⬝ᵥ v = _
    rw [dotProduct_comm, matrixBilinearPairing_eq_dot_mulVec]
  have hf0 : f ≠ 0 := by
    intro hz
    apply hTZ
    funext i
    have he := congrArg (fun g : (Fin 3 → F) →ₗ[F] F => g (Pi.single i 1)) hz
    simpa [f, dotProduct, Pi.single_apply] using he
  have hrpos : 0 < finrank F (LinearMap.range f) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have he : LinearMap.range f = ⊥ := Submodule.finrank_eq_zero.mp hz
    exact hf0 (LinearMap.range_eq_bot.mp he)
  have hle : U ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change f Y = 0
      rw [hf, matrixBilinearPairing_symmetric T hT Y Z,
        matrixBilinearPairing_eq_dot_mulVec, hY, dotProduct_zero]
    · change f Z = 0
      rw [hf, hZ]
  have hr := LinearMap.finrank_range_add_finrank_ker f
  simp only [Module.finrank_pi, Fintype.card_fin] at hr
  have hmono := Submodule.finrank_mono hle
  have heq : U = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  change w ∈ U
  rw [heq]
  change f w = 0
  rw [hf, hw]

end DimensionFourDependence
