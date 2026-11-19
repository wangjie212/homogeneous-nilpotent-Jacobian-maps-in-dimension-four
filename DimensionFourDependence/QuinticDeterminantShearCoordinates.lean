import DimensionFourDependence.ConstructiveDeterminantShearTameness

/-! # Lemma 6.2 in a specified tame coordinate system -/

namespace DimensionFourDependence.Quintic

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄

/-- A tame coordinate frame transports a determinant shear to its
four actual coordinate polynomials. -/
theorem determinant_shear_in_tame_coordinates
    (A : Aut₄) (hA : A ∈ Tame.subgroup K 4) (f : R₃) :
    ∃ E : Aut₄, E ∈ Tame.subgroup K 4 ∧
      let r := A (X 0)
      let s := A (X 1)
      let α := A (X 2)
      let β := A (X 3)
      let q := aeval ![α * r - β * s, α, β] f
      E r = r + β * q ∧ E s = s + α * q ∧ E α = α ∧ E β = β := by
  let F := DeterminantShear.automorphism4 f
  let E := A * F * A⁻¹
  have hE (i : Fin 4) : E (A (X i)) = A (F (X i)) := by
    simp [E, AlgEquiv.mul_apply]
  let r := A (X 0)
  let s := A (X 1)
  let α := A (X 2)
  let β := A (X 3)
  let q := aeval ![α * r - β * s, α, β] f
  let d : R₄ := X 2 * X 0 - X 3 * X 1
  have hv : (fun i : Fin 3 => A.toAlgHom (![d, X 2, X 3] i)) =
      ![α * r - β * s, α, β] := by
    funext i
    fin_cases i
    · change A (X 2 * X 0 - X 3 * X 1) = α * r - β * s
      rw [map_sub, map_mul, map_mul]
    · rfl
    · rfl
  have hp : A (aeval ![d, X 2, X 3] f) = q := by
    change A.toAlgHom (aeval ![d, X 2, X 3] f) = q
    rw [Tame.algHom_aeval, hv]
  refine ⟨E, (Tame.subgroup K 4).mul_mem ((Tame.subgroup K 4).mul_mem hA
    (DeterminantShear.automorphism4_tame f)) ((Tame.subgroup K 4).inv_mem hA), ?_⟩
  change E (A (X 0)) = r + β * q ∧ E (A (X 1)) = s + α * q ∧
    E (A (X 2)) = α ∧ E (A (X 3)) = β
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hE]
    have h : F (X 0) = X 0 + X 3 * aeval ![d, X 2, X 3] f :=
      DeterminantShear.automorphism4_X f 0
    rw [h, map_add, map_mul, hp]
  · rw [hE]
    have h : F (X 1) = X 1 + X 2 * aeval ![d, X 2, X 3] f :=
      DeterminantShear.automorphism4_X f 1
    rw [h, map_add, map_mul, hp]
  · rw [hE]
    exact congrArg A (DeterminantShear.automorphism4_X f 2)
  · rw [hE]
    exact congrArg A (DeterminantShear.automorphism4_X f 3)

end DimensionFourDependence.Quintic
