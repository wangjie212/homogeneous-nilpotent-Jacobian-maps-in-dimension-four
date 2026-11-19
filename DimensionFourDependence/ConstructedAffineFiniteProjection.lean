import DimensionFourDependence.ConstructedMonicProjectionCoordinates
import DimensionFourDependence.MonicAffineFiniteProjection

/-! # A finite linear projection constructed from the original affine equation

An invertible original-field linear change is chosen from the nonzero
equation itself. It preserves the actual generators and relation and
makes the whole original affine chart finite over the actual algebra of
the remaining projection coordinates, without increasing the degree.
-/

namespace DimensionFourDependence

open MvPolynomial

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k A : Type*} [Field k] [Infinite k] [CommRing A] [Algebra k A] {n : ℕ}

/-- A nonzero original affine hypersurface equation constructs an actual
finite linear projection, actual generating coordinates and the full-degree
relation of exactly the original degree. All coordinate and module
finiteness data are constructed from the original affine generators. -/
theorem exists_actual_affine_finite_linear_projection
    (x : Fin (n + 1) → A) (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (f : MvPolynomial (Fin (n + 1)) k) (hf : f ≠ 0) (hroot : aeval x f = 0) :
    ∃ T : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k),
      let r := finSuccEquiv' (0 : Fin (n + 1))
      let y := fun i : Option (Fin n) => linearProjectionCoordinate T x (r.symm i)
      let g := renameEquiv k r
        (linearPolynomialPullback (LinearMap.toMatrix' T.toLinearMap) f)
      Algebra.adjoin k (Set.range y) = ⊤ ∧ g ≠ 0 ∧ g.totalDegree = f.totalDegree ∧
        g.degreeOf none = g.totalDegree ∧ aeval y g = 0 ∧
        Module.Finite (affineProjectionAlgebra (k := k) y) A := by
  obtain ⟨T, hy, hg, hdegree, hfull, hroot'⟩ := exists_actual_monic_projection_coordinates x hx f hf hroot
  refine ⟨T, hy, hg, hdegree, hfull, hroot', ?_⟩
  exact affine_full_degree_projection_finite _ hy _ hg hfull hroot'

end DimensionFourDependence
