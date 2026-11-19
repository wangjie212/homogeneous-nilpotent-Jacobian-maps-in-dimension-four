import DimensionFourDependence.LinearHyperplaneProjectiveGraph
import DimensionFourDependence.ProjectiveNormalizedPrimeCoordinates

/-! # Coordinates of the actual projective hyperplane graph -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type u} {F : Type w} {σ : Type v} [Field E] [Field F] [Algebra E F]

/-- Substitution into the hyperplane graph retains all original
coordinate values, with L as the new homogenizing coordinate. -/
theorem linearHyperplaneGraphHom_aeval
    (L : MvPolynomial σ E) (x : σ → F) (P : MvPolynomial (Option σ) E) :
    aeval x (linearHyperplaneGraphHom L P) =
      aeval (fun j : Option σ => j.elim (aeval x L) x) P := by
  have he : (aeval x).comp (linearHyperplaneGraphHom L) =
      aeval (fun j : Option σ => j.elim (aeval x L) x) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j <;> simp [linearHyperplaneGraphHom]
  exact DFunLike.congr_fun he P

/-- A nonzero source vector remains nonzero after adjoining any
homogenizing coordinate. -/
theorem option_graph_coordinates_ne_zero (x : σ → F) (hx : x ≠ 0) (a : F) :
    (fun j : Option σ => j.elim a x) ≠ 0 := by
  intro hzero
  apply hx
  funext i
  exact congrFun hzero (some i)

/-- On every extension-valued projective point the actual graph
morphism is exactly [X] ↦ [L(X) : X], also when L(X) vanishes. -/
theorem linearHyperplaneProjectiveGraph_fieldPoint
    (L : MvPolynomial σ E) (hL : L.IsHomogeneous 1) (x : σ → F) (hx : x ≠ 0) :
    linearHyperplaneProjectiveGraph L hL (projectiveFieldPoint (E := E) x hx) =
      projectiveFieldPoint (E := E) (fun j : Option σ => j.elim (aeval x L) x)
        (option_graph_coordinates_ne_zero x hx _) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro D P hP
  change P.IsHomogeneous D at hP
  rw [linearHyperplaneProjectiveGraph_mem_iff,
    projectiveFieldPoint_homogeneous_mem x hx (linearHyperplaneGraphHom L P)
      ((linearHyperplaneGraphGradedHom L hL).map_mem hP),
    projectiveFieldPoint_homogeneous_mem _ _ P hP,
    linearHyperplaneGraphHom_aeval]

/-- The same formula holds for original rational coordinate points,
with the original coefficient field on both projective spaces. -/
theorem linearHyperplaneProjectiveGraph_coordinatePoint
    (L : MvPolynomial σ E) (hL : L.IsHomogeneous 1) (x : σ → E) (hx : x ≠ 0) :
    linearHyperplaneProjectiveGraph L hL (projectiveCoordinatePoint x hx) =
      projectiveCoordinatePoint (fun j : Option σ => j.elim (aeval x L) x)
        (option_graph_coordinates_ne_zero x hx _) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro D P hP
  change P.IsHomogeneous D at hP
  have hsub : (linearHyperplaneGraphHom L P).IsHomogeneous D :=
    (linearHyperplaneGraphGradedHom L hL).map_mem hP
  rw [linearHyperplaneProjectiveGraph_mem_iff,
    projectiveCoordinatePoint_mem_homogeneous x hx hsub,
    projectiveCoordinatePoint_mem_homogeneous _ _ hP,
    linearHyperplaneGraphHom_aeval]

/-- With a homogeneous equation, normalized prime coordinates test
the very same projective point's original ideal. -/
theorem projectivePrimeRatioCoordinate_homogeneous_zero_iff
    (z : ProjectiveSpectrum (homogeneousSubmodule σ E)) (a : σ)
    (ha : X a ∉ z.asHomogeneousIdeal) (P : MvPolynomial σ E) {D : ℕ}
    (hP : P.IsHomogeneous D) :
    aeval (projectivePrimeRatioCoordinate z a) P = 0 ↔ P ∈ z.asHomogeneousIdeal := by
  have he := projectiveFieldPoint_homogeneous_mem (K := E) (projectivePrimeRatioCoordinate z a)
    (projectivePrimeRatioCoordinate_ne_zero z a ha) P hP
  rw [projectivePrimeRatioCoordinate_represents z a ha] at he
  exact he.symm

end DimensionFourDependence
