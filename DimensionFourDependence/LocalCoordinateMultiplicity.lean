import DimensionFourDependence.LocalParameterDvr
import DimensionFourDependence.LocalParameterProjectionField
import DimensionFourDependence.DvrPolynomialMultiplicity

/-! # Actual vanishing-coordinate orders from a projection equation

The original vanishing coordinate constructs the source DVR, its local
map, and its actual rational projection field. A polynomial equation for
a generator of the target function field then bounds its multiplicity.
No source DVR, ramification model, or field-degree bound is an input.
-/

namespace DimensionFourDependence

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

variable {k B L : Type*} [Field k] [CharZero k]
  [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B] [Algebra k B]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra k L] [IsScalarTower k B L]

/-- A nonzero vanishing coordinate's actual order is bounded by the
degree of a defining polynomial for a generator over its actual rational
projection field. All local-ring and field comparison maps are built
from that same original coordinate. -/
theorem local_coordinate_order_le_projection_polynomial_degree
    (z : B) (hz0 : z ≠ 0) (hz : z ∈ IsLocalRing.maximalIdeal B) :
    letI : Algebra (FractionRing (Polynomial k)) L := localParameterProjectionFieldAlgebra (k := k) (L := L) z hz0 hz
    ∀ (x : L), IntermediateField.adjoin (FractionRing (Polynomial k)) {x} = ⊤ →
      ∀ (p : Polynomial (FractionRing (Polynomial k))), p ≠ 0 → Polynomial.aeval x p = 0 →
        ∀ (a : ℕ), z ∈ (IsLocalRing.maximalIdeal B) ^ a → a ≤ p.natDegree := by
  letI : Algebra (FractionRing (Polynomial k)) L := localParameterProjectionFieldAlgebra (k := k) (L := L) z hz0 hz
  intro x hgen p hp hroot a horder
  let P := (polynomialParameterZeroPrime k).asIdeal
  let A := Localization.AtPrime P
  let : IsDiscreteValuationRing A := polynomialParameterLocalRing_isDVR k
  let : Algebra (Polynomial k) B := (Polynomial.aeval z).toRingHom.toAlgebra
  let : Algebra (Polynomial k) L := (Polynomial.aeval (algebraMap B L z)).toRingHom.toAlgebra
  let : Algebra A B := (localParameterDvrHom (k := k) z hz).toAlgebra
  let : Algebra A L := ((algebraMap B L).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq (by intro r; rfl)
  let : IsLocalHom (algebraMap A B) := localParameterDvrHom_isLocalHom (k := k) z hz
  let : IsScalarTower (Polynomial k) A B := IsScalarTower.of_algebraMap_eq
    (fun q => (localParameterDvrHom_polynomial (k := k) z hz q).symm)
  let : IsScalarTower (Polynomial k) B L := IsScalarTower.of_algebraMap_eq (by
    intro q
    exact Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k B L) z q)
  let : IsScalarTower (Polynomial k) A L := IsScalarTower.to₁₂₄ (Polynomial k) A B L
  let : Algebra A (FractionRing (Polynomial k)) := primeLocalizationFractionAlgebra (F := FractionRing (Polynomial k)) P
  let : IsScalarTower (Polynomial k) A (FractionRing (Polynomial k)) :=
    primeLocalizationFraction_scalarTower (F := FractionRing (Polynomial k)) P
  let : IsFractionRing A (FractionRing (Polynomial k)) := primeLocalizationFraction_isFractionRing (F := FractionRing (Polynomial k)) P
  let : IsScalarTower (Polynomial k) (FractionRing (Polynomial k)) L := IsScalarTower.of_algebraMap_eq
    (fun q => (localParameterProjectionFieldHom_polynomial (k := k) (L := L) z hz0 hz q).symm)
  let : IsScalarTower A (FractionRing (Polynomial k)) L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext P.primeCompl
    apply RingHom.ext
    intro q
    change algebraMap A L (algebraMap (Polynomial k) A q) =
      algebraMap (FractionRing (Polynomial k)) L (algebraMap A (FractionRing (Polynomial k)) (algebraMap (Polynomial k) A q))
    rw [← IsScalarTower.algebraMap_apply (Polynomial k) A L,
      ← IsScalarTower.algebraMap_apply (Polynomial k) A (FractionRing (Polynomial k)),
      ← IsScalarTower.algebraMap_apply (Polynomial k) (FractionRing (Polynomial k)) L]
  let π : A := algebraMap (Polynomial k) A Polynomial.X
  have hπ : Irreducible π := polynomialParameterLocal_X_irreducible k
  have hvalue : algebraMap A B π = z := localParameterDvrHom_X (k := k) z hz
  have hlocal : algebraMap A B π ∈ (IsLocalRing.maximalIdeal B) ^ a := by
    rw [hvalue]
    exact horder
  exact dominating_dvr_uniformizer_order_le_polynomial_degree
    (A := A) (B := B) (K := FractionRing (Polynomial k)) (L := L) x hgen p hp hroot π hπ a hlocal

end DimensionFourDependence
