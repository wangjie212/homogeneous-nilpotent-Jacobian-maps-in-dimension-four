import DimensionFourDependence.TameShearFactors

/-! # Stable tame group membership for Proposition 6.4 -/

namespace DimensionFourDependence.Shear

open MvPolynomial

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

variable {K : Type*} [Field K]

/-- The reversed pullback of the point-map commutator (6.11). -/
noncomputable def stableAutomorphism5 (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 5) K ≃ₐ[K] MvPolynomial (Fin 5) K :=
  (factorB5 a b f)⁻¹ * (factorA5 a b)⁻¹ * factorB5 a b f * factorA5 a b

/-- The polynomial coordinates of this automorphism are exactly `(Ψ,w)`. -/
theorem stableAutomorphism5_X (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) (j : Fin 5) :
    stableAutomorphism5 a b f (X j) =
      ![X 0 + base5 b * parameter5 a b f, X 1 - base5 a * parameter5 a b f,
        X 2, X 3, X 4] j := by
  have hB (k : Fin 5) : factorB5 a b f (X k) =
      X k + if k = 4 then parameter5 a b f else 0 := Tame.elementary_X _ _ _ k
  have hBi (k : Fin 5) : (factorB5 a b f)⁻¹ (X k) =
      X k + if k = 4 then -parameter5 a b f else 0 := Tame.elementary_inv_X _ _ _ k
  fin_cases j
  · change ((factorB5 a b f)⁻¹ * (factorA5 a b)⁻¹ * factorB5 a b f * factorA5 a b) (X 0) =
      X 0 + base5 b * parameter5 a b f
    exact Tame.commutator_active (factorA5 a b) (factorB5 a b f)
      (X 0) (base5 b) (X 4) (parameter5 a b f)
      (by simpa using factorA5_X a b 0) (by simpa using factorA5_inv_X a b 0)
      (by simp [hB]) (by simp [hBi])
      (factorB5_base a b b f) (factorA5_inv_base a b b) (factorB5_inv_base a b b f)
      (by simp [hB]) (by simpa using factorA5_inv_X a b 4)
      (factorA5_inv_parameter a b f) (factorB5_inv_parameter a b f)
  · change ((factorB5 a b f)⁻¹ * (factorA5 a b)⁻¹ * factorB5 a b f * factorA5 a b) (X 1) =
      X 1 - base5 a * parameter5 a b f
    have h := Tame.commutator_active (factorA5 a b) (factorB5 a b f)
      (X 1) (-base5 a) (X 4) (parameter5 a b f)
      (by simpa [sub_eq_add_neg] using factorA5_X a b 1)
      (by simpa using factorA5_inv_X a b 1)
      (by simp [hB]) (by simp [hBi])
      (by simp only [map_neg, factorB5_base])
      (by simp only [map_neg, factorA5_inv_base])
      (by simp only [map_neg, factorB5_inv_base])
      (by simp [hB]) (by simpa using factorA5_inv_X a b 4)
      (factorA5_inv_parameter a b f) (factorB5_inv_parameter a b f)
    simpa only [neg_mul, sub_eq_add_neg] using h
  · exact Tame.commutator_fixed (factorA5 a b) (factorB5 a b f) (X 2)
      (by simpa using factorA5_X a b 2) (by simp [hB])
  · exact Tame.commutator_fixed (factorA5 a b) (factorB5 a b f) (X 3)
      (by simpa using factorA5_X a b 3) (by simp [hB])
  · exact Tame.commutator_aux (factorA5 a b) (factorB5 a b f) (X 4) (parameter5 a b f)
      (by simpa using factorA5_X a b 4) (by simpa using factorA5_inv_X a b 4)
      (by simp [hB]) (by simpa [sub_eq_add_neg] using hBi 4)
      (factorA5_inv_parameter a b f) (factorB5_inv_parameter a b f)

/-- The stable-tameness assertion of Proposition 6.4, in five variables over
the original coefficient field. The other, unstabilized low-degree assertion
of Proposition 6.4 is a separate result. -/
theorem stableAutomorphism5_tame (a b : MvPolynomial (Fin 2) K)
    (f : MvPolynomial (Fin 3) K) : stableAutomorphism5 a b f ∈ Tame.subgroup K 5 := by
  have hx : factorX5 b ∈ Tame.subgroup K 5 := Tame.elementary_mem _ _ _
  have hy : factorY5 a ∈ Tame.subgroup K 5 := Tame.elementary_mem _ _ _
  have hA : factorA5 a b ∈ Tame.subgroup K 5 := (Tame.subgroup K 5).mul_mem hx hy
  have hB : factorB5 a b f ∈ Tame.subgroup K 5 := Tame.elementary_mem _ _ _
  exact (Tame.subgroup K 5).mul_mem
    ((Tame.subgroup K 5).mul_mem
      ((Tame.subgroup K 5).mul_mem ((Tame.subgroup K 5).inv_mem hB)
        ((Tame.subgroup K 5).inv_mem hA)) hB) hA

end DimensionFourDependence.Shear
