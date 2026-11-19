import DimensionFourDependence.LocalCoordinateMultiplicity
import DimensionFourDependence.ProjectionDefiningPolynomial

/-! # A hypersurface equation bounds the actual local coordinate multiplicity

Independent projection coordinates and the original hypersurface
relation construct a nonzero univariate equation of no larger degree.
The actual local coordinate then has multiplicity at most that original
total degree, with the source DVR and normalization-prime model built
from its given geometric local ring.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k C B L σ : Type*} [Field k] [Field C] [CharZero C] [Algebra k C]
  [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B] [Algebra C B]
  [Field L] [Algebra B L] [IsFractionRing B L]
  [Algebra C L] [IsScalarTower C B L] [Algebra k L] [IsScalarTower k C L]

/-- Given independent projection coordinates and the original
hypersurface relation, every actual vanishing-coordinate order is bounded
by the hypersurface degree. No finite-degree bound or local normalization
isomorphism is supplied as an assumption. -/
theorem local_coordinate_hypersurface_order_le_totalDegree
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    letI : Algebra (FractionRing (Polynomial C)) L :=
      localParameterProjectionFieldAlgebra (k := C) (L := L) z hz0 hz
    ∀ (s : σ → FractionRing (Polynomial C)), AlgebraicIndependent k s →
      ∀ (x : L), IntermediateField.adjoin (FractionRing (Polynomial C)) {x} = ⊤ →
        ∀ (f : MvPolynomial (Option σ) k), f ≠ 0 →
          MvPolynomial.aeval (fun i => i.elim x
            (fun j => algebraMap (FractionRing (Polynomial C)) L (s j))) f = 0 →
          ∀ (a : ℕ), z ∈ (IsLocalRing.maximalIdeal B) ^ a → a ≤ f.totalDegree := by
  letI : Algebra (FractionRing (Polynomial C)) L :=
    localParameterProjectionFieldAlgebra (k := C) (L := L) z hz0 hz
  intro s hs x hgen f hf hroot a horder
  let : IsScalarTower C (FractionRing (Polynomial C)) L := IsScalarTower.of_algebraMap_eq
    (fun c => (localParameterProjectionFieldHom (k := C) (L := L) z hz0 hz).commutes c |>.symm)
  let : IsScalarTower k (FractionRing (Polynomial C)) L :=
    IsScalarTower.to₁₃₄ k C (FractionRing (Polynomial C)) L
  have hp := projectionDefiningPolynomial_ne_zero s hs f hf
  have hr : Polynomial.aeval x (projectionDefiningPolynomial s f) = 0 := by
    rw [projectionDefiningPolynomial_aeval, hroot]
  have hbound := local_coordinate_order_le_projection_polynomial_degree
    (k := C) (L := L) z hz0 hz x hgen (projectionDefiningPolynomial s f) hp hr a horder
  exact hbound.trans (projectionDefiningPolynomial_natDegree_le s f)

end DimensionFourDependence
