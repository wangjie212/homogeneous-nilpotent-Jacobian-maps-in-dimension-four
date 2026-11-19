import DimensionFourDependence.DominatingDvrMultiplicity
import DimensionFourDependence.SimpleFieldDegreeBound

/-! # A defining polynomial bounds the actual local multiplicity

Finiteness and the field-degree bound are constructed from a polynomial
relation for a field generator. The actual dominating normal local ring
then has source-uniformizer order at most that polynomial degree.
-/

namespace DimensionFourDependence

variable {A B K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B]
  [Field K] [CharZero K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L]
  [Algebra A B] [Algebra A L] [Algebra B L] [IsFractionRing B L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsLocalHom (algebraMap A B)]

/-- The original polynomial equation, rather than an assumed field
degree estimate, bounds every actual source-uniformizer order. -/
theorem dominating_dvr_uniformizer_order_le_polynomial_degree
    (x : L) (hgen : IntermediateField.adjoin K {x} = ⊤)
    (p : Polynomial K) (hp : p ≠ 0) (hroot : Polynomial.aeval x p = 0)
    (π : A) (hπ : Irreducible π) (a : ℕ)
    (horder : algebraMap A B π ∈ (IsLocalRing.maximalIdeal B) ^ a) :
    a ≤ p.natDegree := by
  obtain ⟨hfinite, hdegree⟩ := generating_root_finite_and_degree_le x hgen p hp hroot
  let : Module.Finite K L := hfinite
  exact (dominating_dvr_uniformizer_order_le_field_degree (K := K) (L := L) π hπ a horder).trans hdegree

end DimensionFourDependence
