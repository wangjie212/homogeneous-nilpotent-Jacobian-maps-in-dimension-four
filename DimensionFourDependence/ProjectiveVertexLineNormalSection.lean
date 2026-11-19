import DimensionFourDependence.ProjectiveVertexLine
import DimensionFourDependence.ClosedGaussVertexLineIncidence
import DimensionFourDependence.ModifiedCubicFiberBoundary

/-! # The line and vertex lie in one chart, with distinct normal-section values -/

namespace DimensionFourDependence

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

/-- The fourth coordinate remains free on the full vertex line. -/
theorem vertexLinePrime_fourth_coordinate_not_mem
    (b : Fin 3 → K) (j : Fin 3) :
    X (Fin.last 3) ∉ vertexLinePrime b j := by
  intro h
  change vertexLineParameterHom b j (X (Fin.last 3)) = 0 at h
  simp only [vertexLineParameterHom, aeval_X, Fin.snoc_last] at h
  exact X_ne_zero _ h

/-- The actual fixed projective vertex is in the fourth-coordinate chart. -/
theorem fourthAxisProjectivePoint_fourth_coordinate_not_mem (K : Type*) [Field K] :
    X (Fin.last 3) ∉ (fourthAxisProjectivePoint K).asHomogeneousIdeal := by
  intro h
  have he := (projectiveCoordinatePoint_mem_homogeneous
    (Fin.snoc (0 : Fin 3 → K) 1) fourthAxisVector_ne_zero
    (isHomogeneous_X (R := K) (Fin.last 3))).mp h
  apply (one_ne_zero : (1 : K) ≠ 0)
  simpa only [aeval_X, Fin.snoc_last] using he

universe u

set_option quotPrecheck false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type u} [Field K] [CharZero K]
    (H : Fin 4 → MvPolynomial (Fin 4) K) (I : ImageRelationWitness H)
    (E : Type u) [Field E] [Algebra (closedGaussParameterField H I) E]
    [Algebra.IsAlgebraic (closedGaussParameterField H I) E]
    {d : ℕ} (hd : 0 < d) (hH : IsHomogMap H d) (hind : ¬ComponentsDependent H)
    (hGauss : gaussImageDimension H I = 1)
    (hvertex : rationalImageNormal H I.equation (Fin.last 3) = 0)
    (e : RatFunc K ≃ₐ[K] closedGaussParameterField H I)

local notation "ι" => extendedClosedGaussSourceCoefficientHom H I E
local notation "L₀" => linearFormPolynomial
  (extendedClosedGaussChosenRulingMatrix H I E hH hd hind hGauss 0)

include hvertex e

/-- The same actual normal polynomial vanishes at the projective
vertex and is nonzero at the projective line's generic point. Both
points lie in the fourth-coordinate affine chart. -/
theorem actual_normal_section_projective_vertex_line_values
    (b : Fin 3 → K) (hb : b ≠ 0) (j : Fin 3) (hj : b j ≠ 0) :
    (L₀) ∈ (fourthAxisProjectivePoint E).asHomogeneousIdeal ∧
      (L₀) ∉ (vertexLineProjectiveGenericPoint (fun i => (ι) (b i)) j
        ((_root_.map_ne_zero (ι)).mpr hj)).asHomogeneousIdeal ∧
      X (Fin.last 3) ∉ (fourthAxisProjectivePoint E).asHomogeneousIdeal ∧
      X (Fin.last 3) ∉ (vertexLineProjectiveGenericPoint (fun i => (ι) (b i)) j
        ((_root_.map_ne_zero (ι)).mpr hj)).asHomogeneousIdeal := by
  have hinc := actual_closed_gauss_normal_vertex_line_plane_incidence
    H I E hd hH hind hGauss hvertex e b hb j hj
  refine ⟨?_, hinc.2, fourthAxisProjectivePoint_fourth_coordinate_not_mem E,
    vertexLinePrime_fourth_coordinate_not_mem _ j⟩
  exact (projectiveCoordinatePoint_mem_homogeneous
    (Fin.snoc (0 : Fin 3 → E) 1) fourthAxisVector_ne_zero
    (linearFormPolynomial_homogeneous _)).mpr hinc.1

end DimensionFourDependence
