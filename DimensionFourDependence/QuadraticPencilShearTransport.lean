import DimensionFourDependence.NormalizeBinaryQuadraticPencil
import DimensionFourDependence.BinaryPencilActiveConjugacy
import DimensionFourDependence.BinaryPencilBaseTameness
import DimensionFourDependence.PlanarTamenessReduction
import DimensionFourDependence.StableTameConjugacy

/-! # Transporting the normalized quintic family to an arbitrary quadratic pencil -/

namespace DimensionFourDependence.Shear

open Matrix MvPolynomial

set_option maxHeartbeats 1200000

variable {K : Type*} [Field K] [CharZero K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "Aut₄" => R₄ ≃ₐ[K] R₄
local notation "M₂" => Matrix (Fin 2) (Fin 2) K

/-- The actual normalized family of Proposition 6.7. -/
def NormalizedQuadraticPencilShearsTame (K : Type*) [Field K] : Prop :=
  ∀ η c : K,
    automorphism4 (X 0 * X 1) (X 0 ^ 2 + C η * X 1 ^ 2)
      (C c * X 0) ∈ Tame.subgroup K 4

/-- Corollary 6.10 follows from Proposition 6.7 by the actual constant
base coordinate change and the active pencil conjugation. -/
theorem quadratic_pencil_shears_tame_of_normalized
    (hcanonical : NormalizedQuadraticPencilShearsTame K) : QuadraticPencilShearsTame K := by
  intro a b hc ha hb c
  obtain ⟨T, S, hTS, _, m, n, p, q, η, hdet, _, hA, hB⟩ := lemma_6_8 a b hc ha hb
  have hT : IsUnit T.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have h := congrArg Matrix.det hTS
    simp [Matrix.det_mul, hz] at h
  apply scalar_shear_tame_descends_from_binary_base_change T hT a b c
  let α := linearPolynomialPullback T a
  let β := linearPolynomialPullback T b
  let D : M₂ := !![m, p; n, q]
  have hD : IsUnit D.det := by
    apply isUnit_iff_ne_zero.mpr
    simpa [D, Matrix.det_fin_two, mul_comm p n] using hdet
  let E := D⁻¹
  have hDE : D * E = 1 := Matrix.mul_nonsing_inv D hD
  have hED : E * D = 1 := Matrix.nonsing_inv_mul D hD
  have hf₁ : activePencilMatrix D * activePencilMatrix E = 1 := by
    rw [activePencilMatrix_mul, hDE, activePencilMatrix_one]
  have hf₂ : activePencilMatrix E * activePencilMatrix D = 1 := by
    rw [activePencilMatrix_mul, hED, activePencilMatrix_one]
  let H := perturbation4 α β (C c * X 0)
  let G : Aut₄ := automorphism4 (X 0 * X 1) (X 0 ^ 2 + C η * X 1 ^ 2) (C (c * E.det) * X 0)
  have hchange := lemma_6_9 D E hDE hED α β c
  change linearPolynomialConjugate (activePencilMatrix D) (activePencilMatrix E) H =
    perturbation4 (C m * α + C n * β) (C p * α + C q * β) (C (c * E.det) * X 0) at hchange
  rw [show C m * α + C n * β = X 0 * X 1 from hA,
    show C p * α + C q * β = X 0 ^ 2 + C η * X 1 ^ 2 from hB] at hchange
  have hG (j : Fin 4) : G (X j) =
      X j + linearPolynomialConjugate (activePencilMatrix D) (activePencilMatrix E) H j := by
    rw [hchange]
    exact automorphism4_X _ _ _ _
  have hGt : G ∈ Tame.subgroup K 4 := hcanonical η (c * E.det)
  obtain ⟨F, hF, hX⟩ := tame_automorphism_descends_from_constant_linear_conjugacy
    (activePencilMatrix D) (activePencilMatrix E) hf₁ hf₂ H G hG hGt
  have he := actual_automorphisms_with_same_coordinate_perturbation_eq H F
    (automorphism4 α β (C c * X 0)) hX (automorphism4_X _ _ _)
  exact he ▸ hF

end DimensionFourDependence.Shear
