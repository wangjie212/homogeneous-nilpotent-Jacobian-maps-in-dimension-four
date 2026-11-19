import DimensionFourDependence.ComponentSourceRealizationTransport

/-! # One geometric source realization retains the specified coefficient constants -/

namespace DimensionFourDependence

open MvPolynomial

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A chosen actual full generic-fiber component and its exact
intermediate coefficient relations construct one original source
embedding preserving every source value already realized as a specified
constant. Ground coefficients use the same full-output embedding. -/
theorem full_generic_component_constructs_coefficient_compatible_source
    {K C B G Z : Type*} [Field K] [Field C] [Field B] [Field G] [Field Z]
    [Algebra K C] [Algebra C B]
    [Algebra C G] [Algebra K G] [IsScalarTower K C G]
    [Algebra B Z] [Algebra C Z] [IsScalarTower C B Z]
    [Algebra K Z] [IsScalarTower K C Z]
    (H : Fin 4 → MvPolynomial (Fin 4) K)
    (δ : polynomialOutputField H →ₐ[K] C)
    (Φ : FractionRing (MvPolynomial (Fin 4) K) →ₐ[K] G)
    (v : Fin 4 → G) (w : Fin 4 → Z)
    (hΦ : ∀ i, Φ (rationalCoordinate (K := K) i) = v i) :
    letI : Algebra (polynomialOutputField H) B := ((algebraMap C B).comp δ.toRingHom).toAlgebra
    fiberVanishingIdeal (L := B) w ∈
      (extendCoefficientIdeal B (fiberVanishingIdeal (L := polynomialOutputField H)
        (rationalCoordinate (K := K) (n := 4)))).minimalPrimes →
    (fiberVanishingIdeal (L := B) w).comap (MvPolynomial.map (algebraMap C B)) =
      fiberVanishingIdeal (L := C) v →
    ∃ f : FractionRing (MvPolynomial (Fin 4) K) →ₐ[K] Z,
      (∀ i, f (rationalCoordinate (K := K) i) = w i) ∧
      ∀ (c : FractionRing (MvPolynomial (Fin 4) K)) (t : C),
        Φ c = algebraMap C G t → f c = algebraMap C Z t := by
  let D := polynomialOutputField H
  letI : Algebra D B := ((algebraMap C B).comp δ.toRingHom).toAlgebra
  intro hcomponent hcontract
  letI : Algebra D Z := ((algebraMap C Z).comp δ.toRingHom).toAlgebra
  letI : IsScalarTower D B Z := IsScalarTower.of_algebraMap_eq' (by
    ext q
    exact IsScalarTower.algebraMap_apply C B Z (δ q))
  letI : IsScalarTower K D Z := IsScalarTower.of_algebraMap_eq' (by
    ext c
    change algebraMap K Z c = algebraMap C Z (δ (algebraMap K D c))
    rw [δ.commutes]
    exact IsScalarTower.algebraMap_apply K C Z c)
  obtain ⟨fD, hf⟩ := full_generic_component_coordinates_construct_source_realization H w hcomponent
  let f : FractionRing (MvPolynomial (Fin 4) K) →ₐ[K] Z := fD.restrictScalars K
  have hrel : fiberVanishingIdeal (L := C) w = fiberVanishingIdeal (L := C) v := by
    rw [← fiberVanishingIdeal_comap_coefficients (L := C) (E := B)]
    exact hcontract
  refine ⟨f, hf, ?_⟩
  intro c t hc
  exact source_relation_transport_retains_already_constant_values Φ f v w hΦ hf hrel c t hc

end DimensionFourDependence
