import DimensionFourDependence.DegreePreservingPolynomialKernel
import DimensionFourDependence.VertexLineIncidence
import DimensionFourDependence.ProjectiveCoordinatePoint

/-! # The actual projective line prime specializes to the fixed vertex -/

namespace DimensionFourDependence

open MvPolynomial Topology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

/-- The fourth-axis vector represents a projective point. -/
theorem fourthAxisVector_ne_zero : (Fin.snoc (0 : Fin 3 → K) 1 : Fin 4 → K) ≠ 0 := by
  intro hz
  apply (one_ne_zero : (1 : K) ≠ 0)
  simpa only [Fin.snoc_last, Pi.zero_apply] using congrFun hz (Fin.last 3)

/-- The original fixed vertex, as an actual point of Mathlib's projective space. -/
noncomputable def fourthAxisProjectivePoint (K : Type*) [Field K] :
    ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K) :=
  projectiveCoordinatePoint (Fin.snoc (0 : Fin 3 → K) 1) fourthAxisVector_ne_zero

/-- The full line's exact original prime defines its projective generic point. -/
noncomputable def vertexLineProjectiveGenericPoint (b : Fin 3 → K) (j : Fin 3)
    (hj : b j ≠ 0) : ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K) where
  asHomogeneousIdeal :=
    { toSubmodule := vertexLinePrime b j
      is_homogeneous' := vertexLinePrime_isHomogeneous b j }
  isPrime := vertexLinePrime_isPrime b j
  not_irrelevant_le := by
    intro hle
    exact vertexLinePrime_pivot_not_mem b j hj
      (hle (HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < (1 : ℕ) by omega)
        (isHomogeneous_X (R := K) j.castSucc)))

/-- Every equation of the full line belongs to the homogeneous
prime of the actual vertex, including nonhomogeneous equations. -/
theorem vertexLinePrime_le_fourthAxisProjectivePoint
    (b : Fin 3 → K) (j : Fin 3) :
    vertexLinePrime b j ≤ (fourthAxisProjectivePoint K).asHomogeneousIdeal.toIdeal := by
  intro P hP
  change projectivePointLineMap (Fin.snoc (0 : Fin 3 → K) 1) P = 0
  apply Polynomial.ext
  intro d
  rw [projectivePointLineMap_coeff, Polynomial.coeff_zero]
  apply vertexLinePrime_axis_evaluation_zero b j (1 : K)
  have hc := vertexLinePrime_isHomogeneous b j d hP
  change (MvPolynomial.decomposition.decompose' P d : MvPolynomial (Fin 4) K) ∈
    vertexLinePrime b j at hc
  simpa only [MvPolynomial.decomposition.decompose'_apply] using hc

/-- The constructed generic point of every full original vertex
line specializes to the actual fixed projective vertex. -/
theorem vertexLineProjectiveGenericPoint_specializes_vertex
    (b : Fin 3 → K) (j : Fin 3) (hj : b j ≠ 0) :
    vertexLineProjectiveGenericPoint b j hj ⤳ fourthAxisProjectivePoint K := by
  apply specializes_iff_mem_closure.mpr
  apply (ProjectiveSpectrum.le_iff_mem_closure (homogeneousSubmodule (Fin 4) K) _ _).mp
  exact vertexLinePrime_le_fourthAxisProjectivePoint b j

end DimensionFourDependence
