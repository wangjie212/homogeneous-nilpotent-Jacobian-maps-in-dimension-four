import DimensionFourDependence.TernaryPlanarSpecialization
import DimensionFourDependence.PlanarPrimitiveShearFactor

/-! # A homogeneous planar pair with one base variable has an original constant relation -/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 1500000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₃" => MvPolynomial (Fin 3) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "D" => (lastCoordinateAtZero (K := K) (n := 3))

noncomputable def ternaryPlanarJacobian (A : Fin 2 → R₃) : Matrix (Fin 2) (Fin 2) R₃ :=
  Matrix.of fun i j => pderiv j.castSucc (A i)

theorem ternary_planar_jacobian_nilpotent_lifts
    (A : Fin 2 → R₃) (hN : IsNilpotent (ternaryPlanarJacobian A)) :
    IsNilpotent (Shear.planarActiveJacobian (fun i => rename Fin.castSucc (A i))) := by
  let E : R₃ →ₐ[K] R₄ := rename Fin.castSucc
  have he : Shear.planarActiveJacobian (fun i => rename Fin.castSucc (A i)) =
      (ternaryPlanarJacobian A).map E := by
    funext i j
    change pderiv j.castSucc.castSucc (rename Fin.castSucc (A i)) =
      E (pderiv j.castSucc (A i))
    exact pderiv_rename (Fin.castSucc_injective 3) j.castSucc (A i)
  rw [he]
  exact hN.map E.toRingHom.mapMatrix

/-- After subtracting the two active-origin terms, planar dependence
descends to a constant relation because the single base variable gives
the same monomial factor in both coefficients. -/
theorem homogeneous_ternary_planar_normalized_componentsDependent
    (A : Fin 2 → R₃) {d : ℕ} (hA : ∀ i, (A i).IsHomogeneous d)
    (hN : IsNilpotent (ternaryPlanarJacobian A)) :
    ComponentsDependent (fun i => ternaryPlanarNormalized (A i) d) := by
  let B : Fin 2 → R₃ := fun i => ternaryPlanarNormalized (A i) d
  by_cases h₀ : B 0 = 0
  · change ComponentsDependent B
    refine ⟨![1, 0], ?_, ?_⟩
    · intro hz
      have h := congrFun hz (0 : Fin 2)
      simp at h
    · simp [Fin.sum_univ_two, h₀]
  by_cases h₁ : B 1 = 0
  · change ComponentsDependent B
    refine ⟨![0, 1], ?_, ?_⟩
    · intro hz
      have h := congrFun hz (1 : Fin 2)
      simp at h
    · simp [Fin.sum_univ_two, h₁]
  let L : Fin 2 → R₄ := fun i => rename Fin.castSucc (A i)
  have hL (i : Fin 2) : (L i).IsHomogeneous d := (hA i).rename_isHomogeneous
  have hspec (i : Fin 2) : D (Shear.planarActiveNormalized (L i)) = B i :=
    lastCoordinateAtZero_normalized_planar_lift (A i) (hA i)
  have hne (i : Fin 2) (h : B i ≠ 0) : Shear.planarActiveNormalized (L i) ≠ 0 := by
    intro he
    exact h (by rw [← hspec i, he, map_zero])
  obtain ⟨r, a, b, q, _, _, _, _, _, ha, hb, _, hx, hy⟩ :=
    Shear.normalized_planar_pair_constructs_primitive_shear_factor L hL
      (ternary_planar_jacobian_nilpotent_lifts A hN) (hne 0 h₀) (hne 1 h₁)
  let α : K := aeval (![1, 0] : Fin 2 → K) a
  let β : K := aeval (![1, 0] : Fin 2 → K) b
  let Z : R₃ := (X 2) ^ r
  let Q : R₃ := D q
  have hx' : B 0 = C β * Z * Q := by
    have h := congrArg D hx
    simpa only [hspec, map_mul, lastCoordinateAtZero_base4_homogeneous b hb, β, Z, Q] using h
  have hy' : B 1 = -(C α * Z) * Q := by
    have h := congrArg D hy
    simpa only [hspec, map_mul, map_neg, lastCoordinateAtZero_base4_homogeneous a ha, α, Z, Q] using h
  have hβ : β ≠ 0 := by
    intro hz
    exact h₀ (by rw [hx', hz, map_zero, zero_mul, zero_mul])
  change ComponentsDependent B
  refine ⟨![α, β], ?_, ?_⟩
  · intro hz
    exact hβ (congrFun hz (1 : Fin 2))
  · rw [Fin.sum_univ_two]
    change α • B 0 + β • B 1 = 0
    rw [smul_eq_C_mul, smul_eq_C_mul, hx', hy']
    ring

end DimensionFourDependence
