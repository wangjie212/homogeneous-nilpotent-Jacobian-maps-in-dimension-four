import DimensionFourDependence.FixedConeCoordinateConjugacy

/-! # The actual inverse source change preserves vertex parabolas

The source-field inverse is the inverse constant matrix substitution.
Its projected coordinates remain affine in the actual fiber parameter,
and its vertex coordinate is unchanged. Every transformed coefficient
is constructed in the original geometric coefficient field.
-/

namespace DimensionFourDependence

open MvPolynomial Matrix

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {K : Type*} [Field K] {n : ℕ}

/-- The inverse source-field equivalence is the source substitution
defined by the actual inverse coordinate matrix. -/
theorem matrixSourceFractionEquiv_symm
    (T S : Matrix (Fin n) (Fin n) K) (hTS : T * S = 1) (hST : S * T = 1) :
    (matrixSourceFractionEquiv T S hTS hST).symm = matrixSourceFractionEquiv S T hST hTS := by
  unfold matrixSourceFractionEquiv
  rw [IsFractionRing.algEquivOfAlgEquiv_symm]
  rfl

/-- The inverse block source change acts on every projected coordinate
by the actual inverse transverse matrix, with no vertex-coordinate term. -/
theorem vertex_preserving_source_inverse_transverse_coordinate
    (T S : Matrix (Fin n) (Fin n) K)
    (hTS : vertexPreservingMatrix T * vertexPreservingMatrix S = 1)
    (hST : vertexPreservingMatrix S * vertexPreservingMatrix T = 1) (i : Fin n) :
    (matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST).symm
      (rationalCoordinate (K := K) i.castSucc) =
      ∑ j : Fin n, algebraMap K (FractionRing (MvPolynomial (Fin (n + 1)) K)) (S i j) *
        rationalCoordinate (K := K) j.castSucc := by
  rw [matrixSourceFractionEquiv_symm, matrixSourceFractionEquiv_coordinate, Fin.sum_univ_castSucc]
  simp [vertexPreservingMatrix]

/-- The original vertex coordinate is fixed by the inverse source change. -/
theorem vertex_preserving_source_inverse_vertex_coordinate
    (T S : Matrix (Fin n) (Fin n) K)
    (hTS : vertexPreservingMatrix T * vertexPreservingMatrix S = 1)
    (hST : vertexPreservingMatrix S * vertexPreservingMatrix T = 1) :
    (matrixSourceFractionEquiv (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST).symm
      (rationalCoordinate (K := K) (Fin.last n)) = rationalCoordinate (K := K) (Fin.last n) := by
  rw [matrixSourceFractionEquiv_symm, matrixSourceFractionEquiv_coordinate]
  simp [vertexPreservingMatrix_last_row]

variable {E G : Type*} [Field E] [Field G] [Algebra K E] [Algebra K G]
    [Algebra E G] [IsScalarTower K E G]

/-- An actual source-field realization of a vertex parabola transports
through the inverse source change to another parabola with the same
quadratic vertex polynomial. Its new affine projected coefficients are
constructed over the same actual geometric constants. -/
theorem vertex_preserving_inverse_source_realization_parabola
    (f : FractionRing (MvPolynomial (Fin 4) K) →ₐ[K] G)
    (z : Fin 4 → G) (hf : ∀ i, f (rationalCoordinate (K := K) i) = z i)
    (T S : Matrix (Fin 3) (Fin 3) K)
    (hTS : vertexPreservingMatrix T * vertexPreservingMatrix S = 1)
    (hST : vertexPreservingMatrix S * vertexPreservingMatrix T = 1)
    (t : G) (x A : Fin 3 → E)
    (hx : ∀ i : Fin 3, z i.castSucc = algebraMap E G (x i) + algebraMap E G (A i) * t) :
    let ψ := f.comp (matrixSourceFractionEquiv
      (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST).symm.toAlgHom
    ∃ x' A' : Fin 3 → E,
      (∀ i : Fin 3, ψ (rationalCoordinate (K := K) i.castSucc) =
        algebraMap E G (x' i) + algebraMap E G (A' i) * t) ∧
      ψ (rationalCoordinate (K := K) (Fin.last 3)) = z (Fin.last 3) := by
  let ψ := f.comp (matrixSourceFractionEquiv
    (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST).symm.toAlgHom
  let x' : Fin 3 → E := fun i => ∑ j : Fin 3, algebraMap K E (S i j) * x j
  let A' : Fin 3 → E := fun i => ∑ j : Fin 3, algebraMap K E (S i j) * A j
  refine ⟨x', A', ?_, ?_⟩
  · intro i
    change f ((matrixSourceFractionEquiv
      (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST).symm
        (rationalCoordinate (K := K) i.castSucc)) = _
    rw [vertex_preserving_source_inverse_transverse_coordinate]
    simp only [map_sum, map_mul, f.commutes, hf, hx, x', A',
      ← IsScalarTower.algebraMap_apply K E G, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · change f ((matrixSourceFractionEquiv
      (vertexPreservingMatrix T) (vertexPreservingMatrix S) hTS hST).symm
        (rationalCoordinate (K := K) (Fin.last 3))) = _
    rw [vertex_preserving_source_inverse_vertex_coordinate, hf]

end DimensionFourDependence
