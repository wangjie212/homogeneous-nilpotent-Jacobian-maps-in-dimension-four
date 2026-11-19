import DimensionFourDependence.ActivePencilLinearFrame
import DimensionFourDependence.BinaryPencilDeterminantIdentity

/-! # The active block of the actual linear conjugation in Lemma 6.9 -/

namespace DimensionFourDependence.Shear

open Matrix MvPolynomial

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "M₂" => Matrix (Fin 2) (Fin 2) K

theorem activePencilMatrix_conjugate_active (T S : M₂) (H : Fin 4 → R₄)
    (h2 : H 2 = 0) (h3 : H 3 = 0) (i : Fin 2) :
    linearPolynomialConjugate (activePencilMatrix T) (activePencilMatrix S) H i.castSucc.castSucc =
      ∑ j : Fin 2, C (S i j) *
        linearPolynomialPullback (activePencilMatrix T) (H j.castSucc.castSucc) := by
  unfold linearPolynomialConjugate
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hz2 : H (Fin.last 2).castSucc = 0 := h2
  have hz3 : H (Fin.last 3) = 0 := h3
  simp only [hz2, hz3, linearPolynomialPullback, map_zero, mul_zero, add_zero,
    activePencilMatrix_active_block]

theorem activePencilMatrix_conjugate_last (T S : M₂) (H : Fin 4 → R₄) (hz : H 3 = 0) :
    linearPolynomialConjugate (activePencilMatrix T) (activePencilMatrix S) H 3 = 0 :=
  vertexPreserving_conjugate_last_zero (vertexPreservingMatrix T) (vertexPreservingMatrix S) H hz

theorem activePencilMatrix_conjugate_penultimate (T S : M₂) (H : Fin 4 → R₄)
    (h2 : H 2 = 0) (h3 : H 3 = 0) :
    linearPolynomialConjugate (activePencilMatrix T) (activePencilMatrix S) H 2 = 0 := by
  change linearPolynomialConjugate (activePencilMatrix T) (activePencilMatrix S) H
    (Fin.last 2).castSucc = 0
  unfold linearPolynomialConjugate
  rw [Fin.sum_univ_castSucc]
  have hz3 : H (Fin.last 3) = 0 := h3
  simp only [hz3, linearPolynomialPullback, map_zero, mul_zero, add_zero,
    activePencilMatrix, vertexPreservingMatrix_castSucc, vertexPreservingMatrix_last_row]
  rw [Fin.sum_univ_castSucc]
  simp [h2, Fin.castSucc_ne_last]

theorem scalar_linear_shear_perturbation (a b : R₂) (c : K) :
    perturbation4 a b (C c * X 0) =
      ![C c * base4 b * invariant4 a b, -(C c * base4 a * invariant4 a b), 0, 0] := by
  have hp : parameter4 a b (C c * X 0) = C c * invariant4 a b := by
    simp [parameter4]
  rw [perturbation4, hp]
  have h (u v w : R₄) : u * (v * w) = v * u * w := by ring
  simp only [h]

end DimensionFourDependence.Shear
