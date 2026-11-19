import DimensionFourDependence.FixedCoordinateChartLinearConjugacy
import DimensionFourDependence.PlanarPrimitiveShearFactor

/-! # Lifting a binary active-coordinate change to the full polynomial ring -/

namespace DimensionFourDependence.Shear

open MvPolynomial Matrix

variable {K : Type*} [Field K]
local notation "R₂" => MvPolynomial (Fin 2) K
local notation "R₄" => MvPolynomial (Fin 4) K
local notation "M₂" => Matrix (Fin 2) (Fin 2) K
local notation "M₄" => Matrix (Fin 4) (Fin 4) K

noncomputable def activePencilMatrix (T : M₂) : M₄ :=
  vertexPreservingMatrix (vertexPreservingMatrix T)

theorem activePencilMatrix_mul (T S : M₂) :
    activePencilMatrix T * activePencilMatrix S = activePencilMatrix (T * S) := by
  simp only [activePencilMatrix, vertexPreservingMatrix_mul]

theorem activePencilMatrix_one : activePencilMatrix (1 : M₂) = 1 := by
  simp only [activePencilMatrix, vertexPreservingMatrix_one]

theorem activePencilMatrix_active_block (T : M₂) (i j : Fin 2) :
    activePencilMatrix T i.castSucc.castSucc j.castSucc.castSucc = T i j := by
  simp only [activePencilMatrix, vertexPreservingMatrix_castSucc]

theorem activePencilMatrix_pullback_last (T : M₂) :
    linearPolynomialPullback (activePencilMatrix T) (X 3 : R₄) = X 3 :=
  vertexPreservingMatrix_vertex_pullback (vertexPreservingMatrix T)

theorem activePencilMatrix_pullback_penultimate (T : M₂) :
    linearPolynomialPullback (activePencilMatrix T) (X 2 : R₄) = X 2 := by
  change linearPolynomialPullback (vertexPreservingMatrix (vertexPreservingMatrix T))
    (X (Fin.last 2).castSucc : R₄) = X (Fin.last 2).castSucc
  rw [← rename_X, vertexPreservingMatrix_transverse_pullback,
    vertexPreservingMatrix_vertex_pullback]

theorem activePencilMatrix_pullback_base (T : M₂) (a : R₂) :
    linearPolynomialPullback (activePencilMatrix T) (base4 a) = base4 a := by
  let E : R₄ →ₐ[K] R₄ := aeval (linearPolynomialMap (activePencilMatrix T))
  let B : R₂ →ₐ[K] R₄ := aeval ![X 2, X 3]
  have he : E.comp B = B := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [B, AlgHom.comp_apply, aeval_X]
    fin_cases i
    · exact activePencilMatrix_pullback_penultimate T
    · exact activePencilMatrix_pullback_last T
  exact AlgHom.congr_fun he a

theorem activePencilMatrix_pullback_active (T : M₂) (i : Fin 2) :
    linearPolynomialPullback (activePencilMatrix T) (X i.castSucc.castSucc : R₄) =
      ∑ j : Fin 2, C (T i j) * X j.castSucc.castSucc := by
  simp only [linearPolynomialPullback, aeval_X, linearPolynomialMap]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [activePencilMatrix, vertexPreservingMatrix_castSucc, vertexPreservingMatrix,
    Fin.lastCases_last, Fin.lastCases_castSucc, map_zero, zero_mul, add_zero]

end DimensionFourDependence.Shear
